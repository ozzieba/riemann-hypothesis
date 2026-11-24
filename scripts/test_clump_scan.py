"""Regressions for scope/declaration scanning during clump generation.

Run with `LEAN=/path/to/lean python3 -m unittest discover -s scripts -p test_clump_scan.py`
to include a stock-Lean before/after compilation of the generated fixture.
"""

import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

import clump


LITERAL_CASES = {
    "ordinary": 'def marker : String := "/-"',
    "escaped_quote": r'def marker : String := "\"/-"',
    "escaped_backslash": r'def marker : String := "\\/-"',
    "multiline": 'def marker : String := "\nnamespace Phantom\n/-\nend Phantom\n"',
    "raw": r'def marker : String := r"\"',
    "raw_hash": 'def marker : String := r#"" /-"#',
    "raw_hashes": 'def marker : String := r##""# /-"##',
    "line_comment": '-- /- a line comment is not a block comment',
    "quote_char": "def marker : Char := '\"'\n-- /-",
    "escaped_char": r"def marker : Char := '\x22'" + '\n-- /-',
    "quoted_name": 'def «/-» : Nat := 0',
    "interpolated": 'def marker : String := s!"{\"/-\"}"',
    "nested_interpolated": 'def marker : String := s!"{s!"{\"/-\"}"}"',
    "spaced_interpolated": 'def marker : String := s! "{\"/-\"}"',
    "commented_interpolated": 'def marker : String := s! /- prefix comment -/ "{\"/-\"}"',
    "dbg_trace_interpolated": 'def marker : Nat := dbg_trace "{\"/-\"}"; 2',
    "ordinary_bang_function": 'def consume! (s : String) : String := s\ndef marker : String := consume! "{"',
}


def body_for(name, snippet):
    return f"namespace {name}\n{snippet}\ndef after : Nat := 37\nend {name}\n"


class ScopeScanTests(unittest.TestCase):
    def test_literals_do_not_hide_scope_ends_or_declarations(self):
        for label, snippet in LITERAL_CASES.items():
            with self.subTest(label=label):
                scopes, decls = clump.scan(body_for("Example", snippet))
                self.assertEqual(scopes, [])
                self.assertIn("Example.after", decls)
                self.assertNotIn("Phantom", str(decls))
        self.assertIn("Example.«/-»", clump.scan(body_for("Example", LITERAL_CASES["quoted_name"]))[1])

    def test_nested_comments_ignore_quotes_and_line_comment_markers(self):
        body = (
            'namespace Example\n'
            '/- " -- /- nested block\n'
            'namespace Phantom\n'
            '-/ outer block remains\n'
            'end Phantom\n'
            '-/\n'
            'def after : Nat := 37\n'
            'end Example -- /- ignored at the end of a command\n'
        )
        self.assertEqual(clump.scan(body), ([], {"Example.after"}))

    def test_real_open_scopes_and_primed_names_remain_visible(self):
        body = "section\nnamespace Example\ndef marker' : String := \"/-\"\ndef after' := 37\n"
        self.assertEqual(clump.scan(body),
                         ([("section", None), ("namespace", "Example")],
                          {"Example.marker'", "Example.after'"}))

    def test_literals_cannot_hide_a_declaration_clash(self):
        # Private names may coexist in separate modules, but collide after folding.
        base = "module\n\nnamespace Example\ndef marker : String := \"/-\"\nprivate def shared : Nat := 37\nend Example\n"
        use = "module\n\nimport Toy.Base\n\nnamespace Example\nprivate def shared : Nat := 37\nend Example\n"
        mods = {
            "Toy.Base": clump.Module("Toy.Base", "src/Toy/Base.lean", base),
            "Toy.Use": clump.Module("Toy.Use", "src/Toy/Use.lean", use),
        }
        self.assertEqual(clump.plan(mods, 2000), {})

    def test_generated_clump_and_consumer_compile(self):
        lean = os.environ.get("LEAN") or shutil.which("lean")
        if not lean:
            self.skipTest("Set LEAN to include the stock-Lean compilation check")
        lean = str(Path(lean).resolve())
        bodies = [body_for(f"ScopeCase{i}", snippet)
                  for i, snippet in enumerate(LITERAL_CASES.values())]
        files = {
            "Toy.Base": "module\n\n@[expose] public section\n" + "\n".join(bodies),
            "Toy.Use": "module\n\npublic import Toy.Base\n\n@[expose] public section\n"
                       "theorem useAfter : ScopeCase0.after = 37 := rfl\n",
            "Other.Consumer": "module\n\npublic import Toy.Use\n\n@[expose] public section\n"
                              "theorem consume : ScopeCase0.after = 37 := useAfter\n",
        }
        with tempfile.TemporaryDirectory(prefix="clump-scan-") as tmp:
            root = Path(tmp)
            src = root / "src"
            for name, content in files.items():
                path = src.joinpath(*name.split(".")).with_suffix(".lean")
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(content, encoding="utf-8")
            subprocess.run(["git", "init", "-q", str(root)], check=True)
            subprocess.run(["git", "-C", str(root), "add", "src"], check=True)
            env = {**os.environ, "LEAN_PATH": str(src)}

            def compile_module(name):
                path = Path(*name.split("."))
                result = subprocess.run(
                    [lean, "-o", str(path.with_suffix(".olean")), str(path.with_suffix(".lean"))],
                    cwd=src, env=env, text=True, capture_output=True,
                )
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

            for name in files:
                compile_module(name)
            mods = clump.load(str(root))
            planned = clump.plan(mods, 2000)
            self.assertEqual(planned, {"Toy.Use": ["Toy.Base", "Toy.Use"]})
            clump.apply(str(root), planned)
            combined = (src / "Toy/Use.lean").read_text(encoding="utf-8")
            self.assertEqual(clump.unclump_text(combined),
                             {name: files[name] for name in ("Toy.Base", "Toy.Use")})
            # Ensure the generated build cannot use the pre-clump object files.
            for pattern in ("*.olean", "*.olean.*", "*.ilean"):
                for path in src.rglob(pattern):
                    path.unlink()
            compile_module("Toy.Use")
            compile_module("Other.Consumer")


if __name__ == "__main__":
    unittest.main()
