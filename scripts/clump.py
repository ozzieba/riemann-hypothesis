#!/usr/bin/env python3
"""Combine small modules into larger files ("clumps") along the import graph, and undo it.

A clump is a coarsening of the import graph: a module R (the clump root) together with
modules whose only project importer lies inside the clump.  Contracting such a set can never
create an import cycle, and every module outside the clump that imported a member imported R,
so the clump file keeps R's module name and path.  No importer anywhere needs rewriting; the
other members' files are deleted.

The clump file is a linearisation of the clump (dependencies first, R last).  Each member is
written verbatim between seam markers, inside its own `section ... end`, with any sections or
namespaces it left open closed explicitly:

    -- ===== clump member: A.B.C =====
    -- clump-header: {"m": "A.B.C", "h": "module\\n\\npublic import X\\n..."}
    section
    <original body of A/B/C.lean, verbatim>
    end -- clump:auto
    -- ===== end clump member: A.B.C =====

`clump.py unclump` splits clump files back into the original files, byte for byte, provided
the member bodies were not edited.  If they were, it still restores the edited bodies; the
original import headers are restored as recorded.

Usage:
    clump.py plan   ROOT [--max-lines N] [--out plan.json]
    clump.py apply  ROOT plan.json
    clump.py unclump ROOT
    clump.py blame  ROOT build.log...   # members containing build errors, for clump-exclude.txt

Members that fail to compile once clumped (e.g. because a sibling member's declarations or
imports change how a name resolves) are listed in scripts/clump-exclude.txt and stay standalone.
"""

import argparse
import collections
import json
import os
import re
import subprocess
import sys

SEAM_BEGIN = "-- ===== clump member: "
SEAM_END = "-- ===== end clump member: "
HEADER_TAG = "-- clump-header: "
AUTO = " -- clump:auto"
CLUMP_MARK = "-- This file was produced by scripts/clump.py from the modules listed below."

# Modules in these libraries are never clumped (protected statement / solution files).
PROTECTED_LIBS = {"Main", "Challenge"}

IMPORT_RE = re.compile(r"^((?:(?:public|private|meta)\s+)*)import\s+((?:all\s+)?)(\S+)\s*$")


def lib_of(mod):
    """Return the lake library a module belongs to (mirrors lakefile.toml)."""
    if mod in ("Statements", "Main"):
        return "Main"
    if mod == "Challenge":
        return "Challenge"
    parts = mod.split(".")
    if parts[0] == "GroundTheory" and len(parts) > 1 and parts[1] in ("LocalFields", "GlobalFields"):
        return "GroundTheoryFields"
    return parts[0]


class Module:
    __slots__ = ("name", "path", "header", "body", "imports", "lines", "exotic", "decls")

    def __init__(self, name, path, text):
        self.name = name
        self.path = path
        lines = text.split("\n")
        h = 0
        imports = []  # (module, public: bool)
        exotic = False
        for i, l in enumerate(lines):
            s = l.strip()
            if s == "" or s == "module":
                continue
            m = IMPORT_RE.match(s)
            if m:
                mods = m.group(1).split()
                if m.group(2) or "meta" in mods:
                    exotic = True
                imports.append((m.group(3), "public" in mods))
                continue
            h = i
            break
        else:
            h = len(lines)
        self.header = "\n".join(lines[:h]) + ("\n" if h < len(lines) else "")
        self.body = "\n".join(lines[h:])
        self.imports = imports
        # Size counts the body plus seam overhead; imports are deduplicated in the clump header.
        stack, self.decls = scan(self.body)
        self.lines = self.body.count("\n") + 6 + len(stack)
        self.exotic = exotic


def load(root):
    out = subprocess.run(["git", "-C", root, "ls-files", "-z", "src/*.lean"],
                         capture_output=True, check=True).stdout.decode()
    mods = {}
    for p in out.split("\0"):
        if not p:
            continue
        name = p[len("src/"):-len(".lean")].replace("/", ".")
        with open(os.path.join(root, p), encoding="utf-8") as f:
            mods[name] = Module(name, p, f.read())
    return mods


# ---------------------------------------------------------------------------
# Planning

def plan(mods, max_lines, exclude=frozenset()):
    deps = {m: list(dict.fromkeys(x for x, _ in mods[m].imports if x in mods)) for m in mods}
    rev = collections.defaultdict(list)
    for m, ds in deps.items():
        for x in ds:
            rev[x].append(m)

    def clumpable(m):
        return (lib_of(m) not in PROTECTED_LIBS and not mods[m].exotic and m not in exclude
                and not is_clump_file(mods[m]))

    # Reverse topological order: dependencies before importers.
    indeg = {m: len(deps[m]) for m in mods}
    ready = sorted(m for m in mods if indeg[m] == 0)
    order = []
    while ready:
        m = ready.pop()
        order.append(m)
        for u in rev[m]:
            indeg[u] -= 1
            if indeg[u] == 0:
                ready.append(u)
    if len(order) != len(mods):
        sys.exit("import graph has a cycle")

    members = {m: [m] for m in mods}
    body = {m: mods[m].lines for m in mods}  # summed body lines of the clump rooted here
    imps = {m: {x for x, _ in mods[m].imports} for m in mods}  # union of members' imports
    names = {m: mods[m].decls for m in mods}  # top-level declaration names in the clump

    def total(b, i, mem):  # output lines: header (deduplicated imports) + bodies
        return b + len(i) - len(mem) + 6

    absorbed = set()
    clashes = [0]
    for v in order:
        if not clumpable(v):
            continue
        kids = [c for c in deps[v]
                if rev[c] == [v] and clumpable(c) and lib_of(c) == lib_of(v)]
        kids.sort(key=lambda c: (body[c], c))
        for c in kids:
            b = body[v] + body[c]
            i = imps[v] | imps[c]
            mem = members[v] + members[c]
            if total(b, i, mem) > max_lines:
                continue
            if not names[v].isdisjoint(names[c]):
                # Declarations that coexisted in separate modules (private ones, or
                # duplicates that no single module ever imported together) clash in one file.
                clashes[0] += 1
                continue
            body[v], imps[v], members[v] = b, i, mem
            names[v] = names[v] | names[c]
            absorbed.add(c)
    print(f"refused {clashes[0]} folds because of clashing declaration names", file=sys.stderr)
    clumps = {}
    for r in mods:
        if r in absorbed or len(members[r]) == 1:
            continue
        clumps[r] = linearise(r, set(members[r]), deps)
    return clumps


def linearise(root, mem, deps):
    """DFS post-order from the root over imports inside the clump: dependencies first."""
    seen, out = set(), []
    stack = [(root, iter(deps[root]))]
    seen.add(root)
    while stack:
        m, it = stack[-1]
        for x in it:
            if x in mem and x not in seen:
                seen.add(x)
                stack.append((x, iter(deps[x])))
                break
        else:
            stack.pop()
            out.append(m)
    assert set(out) == mem and out[-1] == root
    return out


# ---------------------------------------------------------------------------
# Scope tracking: which sections / namespaces does a body leave open?

SECTION_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:(?:public|private|noncomputable|meta)\s+)*section(?:\s+([^\s-]\S*))?\s*(?:--.*)?$")
NAMESPACE_RE = re.compile(r"^namespace\s+(\S+)\s*(?:--.*)?$")
END_RE = re.compile(r"^end(?:\s+([^\s-]\S*))?\s*(?:--.*)?$")
MUTUAL_RE = re.compile(r"^mutual\s*(?:--.*)?$")


DECL_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*"
    r"(?:(?:private|protected|noncomputable|partial|unsafe|public|nonrec|scoped|local)\s+)*"
    r"(?:def|theorem|lemma|abbrev|instance|structure|class|inductive|opaque|axiom|irreducible_def)"
    r"\s+([^\s:({\[]+)")

CHAR_LITERAL_RE = re.compile(r"'(?:[^'\\\n]|\\(?:u[0-9a-fA-F]{4}|x[0-9a-fA-F]{2}|[^\n]))'")
RAW_STRING_RE = re.compile(r'r(#+)?"')
INTERPOLATED_PREFIXES = {"s!", "m!", "f!", "println!", "dbg_trace", "throwError"}


def scan_code(body):
    """Mask comments and literals for the approximate command scan, preserving columns.

    Keep quoted identifiers intact: they can contain comment delimiters, but their
    contents are still part of a declaration's name. Recognise the standard immediate
    interpolation prefixes; this remains an approximation, not a parser for custom
    Lean syntax. Interpolation expressions cannot contain module-level commands.
    """
    out = list(body)
    n, i, depth = len(body), 0, 0
    # Literal frames are (closing delimiter, interpolated, escapes); expression frames are
    # integers counting braces inside an interpolated string.
    frames = []
    last_token = None

    def mask(a, b):
        for j in range(a, b):
            if out[j] != "\n":
                out[j] = " "

    def id_char(c):
        return c.isalnum() or c in "_.'!?"

    while i < n:
        if depth:
            if body.startswith("/-", i):
                depth += 1
                end = i + 2
            elif body.startswith("-/", i):
                depth -= 1
                end = i + 2
            else:
                end = i + 1
            mask(i, end)
            i = end
            continue
        if frames and isinstance(frames[-1], tuple):
            delim, interp, escapes = frames[-1]
            if body.startswith(delim, i):
                end = i + len(delim)
                frames.pop()
                last_token = None
            elif escapes and body[i] == "\\":
                end = min(i + 2, n)
            elif interp and body[i] == "{":
                frames.append(1)
                last_token = None
                end = i + 1
            else:
                end = i + 1
            mask(i, end)
            i = end
            continue
        if body.startswith("--", i):
            end = body.find("\n", i)
            end = n if end < 0 else end
            mask(i, end)
            i = end
            continue
        if body.startswith("/-", i):
            depth = 1
            mask(i, i + 2)
            i += 2
            continue
        if body[i] == "«":
            end = body.find("»", i + 1)
            end = n if end < 0 else end + 1
            if frames:
                mask(i, end)
            last_token = body[i:end]
            i = end
            continue
        # Do not mistake an identifier's prime for a character-literal opener.
        if body[i] == "'" and (i == 0 or not id_char(body[i - 1])):
            m = CHAR_LITERAL_RE.match(body, i)
            if m:
                end = m.end()
                mask(i, end)
                last_token = None
                i = end
                continue
        if body[i] == "r" and (i == 0 or not id_char(body[i - 1])):
            m = RAW_STRING_RE.match(body, i)
            if m:
                frames.append(('"' + (m.group(1) or ""), False, False))
                end = m.end()
                mask(i, end)
                last_token = None
                i = end
                continue
        if id_char(body[i]):
            end = i + 1
            while end < n and id_char(body[end]):
                end += 1
            last_token = body[i:end]
            if frames:
                mask(i, end)
            i = end
            continue
        if body[i] == '"':
            frames.append(('"', last_token in INTERPOLATED_PREFIXES, True))
            last_token = None
            mask(i, i + 1)
        elif frames:
            if body[i] == "{":
                frames[-1] += 1
            elif body[i] == "}":
                frames[-1] -= 1
                if frames[-1] == 0:
                    frames.pop()
            mask(i, i + 1)
        if not body[i].isspace():
            last_token = None
        i += 1
    return "".join(out)


def scan(body):
    """Return (scopes left open at the end of `body`, set of full names declared at top level).

    Line-based and approximate: commands are recognised only at column 0, outside comments/literals.
    """
    stack = []
    decls = set()
    for l in scan_code(body).split("\n"):
        if not l.startswith((" ", "\t")) and l:
            m = SECTION_RE.match(l)
            if m:
                stack.append(("section", m.group(1)))
            else:
                m = NAMESPACE_RE.match(l)
                if m:
                    stack.append(("namespace", m.group(1)))
                elif MUTUAL_RE.match(l):
                    stack.append(("mutual", None))
                else:
                    m = END_RE.match(l)
                    if m and stack:
                        stack.pop()
                    else:
                        m = DECL_RE.match(l)
                        if m and not m.group(1).startswith(("where", ":=")):
                            name = m.group(1)
                            if name.startswith("_root_."):
                                decls.add(name[len("_root_."):])
                            else:
                                ns = ".".join(n for k, n in stack if k == "namespace")
                                decls.add(ns + "." + name if ns else name)
    return stack, decls


def open_scopes(body):
    return scan(body)[0]


def closers(stack):
    out = []
    for kind, name in reversed(stack):
        if kind == "mutual":
            raise ValueError("unterminated mutual block")
        out.append(("end " + name if name else "end") + AUTO)
    return out


# ---------------------------------------------------------------------------
# Applying

def is_clump_file(mod):
    return CLUMP_MARK in mod.body.split("\n", 3)[0:3] or SEAM_BEGIN in mod.body


def render(root, order, mods):
    mem = set(order)
    by = {m: mods[m] for m in order}
    # A clump-external import is public iff some member imported it publicly: public
    # statements in an `@[expose] public section` may only mention publicly imported names.
    ext = {}
    for m in order:
        for x, pub in by[m].imports:
            if x in mem:
                continue
            ext[x] = ext.get(x, False) or pub
    pubs = [x for x in ext if ext[x]]
    privs = [x for x in ext if not ext[x]]
    out = ["module", ""]
    out += ["public import " + x for x in pubs]
    out += ["import " + x for x in privs]
    out += ["", CLUMP_MARK]
    out += ["-- Members: " + ", ".join(order), ""]
    for m in order:
        mod = by[m]
        body = mod.body
        trailing_nl = body.endswith("\n")
        if trailing_nl:
            body = body[:-1]
        info = {"m": m, "h": mod.header}
        if not trailing_nl:
            info["nonl"] = True
        out.append(SEAM_BEGIN + m + " =====")
        out.append(HEADER_TAG + json.dumps(info, ensure_ascii=False))
        out.append("section" + AUTO)
        out.append(body)
        out += closers(open_scopes(body))
        out.append("end" + AUTO)
        out.append(SEAM_END + m + " =====")
        out.append("")
    return "\n".join(out)


def apply(root, clumps):
    mods = load(root)
    for r, order in clumps.items():
        text = render(r, order, mods)
        for m in order:
            if m != r:
                os.remove(os.path.join(root, mods[m].path))
        with open(os.path.join(root, mods[r].path), "w", encoding="utf-8") as f:
            f.write(text)


# ---------------------------------------------------------------------------
# Unclumping

def unclump_text(text):
    lines = text.split("\n")
    i, out = 0, {}
    while i < len(lines):
        if not lines[i].startswith(SEAM_BEGIN):
            i += 1
            continue
        info = json.loads(lines[i + 1][len(HEADER_TAG):])
        name = info["m"]
        j = i + 2
        assert lines[j] == "section" + AUTO, (name, lines[j])
        k = j + 1
        while lines[k] != SEAM_END + name + " =====":
            k += 1
        body = [l for l in lines[j + 1:k] if not l.endswith(AUTO)]
        body = "\n".join(body) + ("" if info.get("nonl") else "\n")
        out[name] = info["h"] + body
        i = k + 1
    return out


def unclump(root):
    out = subprocess.run(["git", "-C", root, "ls-files", "-z", "--cached", "--others",
                          "--exclude-standard", "src/*.lean"],
                         capture_output=True, check=True).stdout.decode()
    n = 0
    for p in out.split("\0"):
        if not p or not os.path.exists(os.path.join(root, p)):
            continue
        with open(os.path.join(root, p), encoding="utf-8") as f:
            text = f.read()
        if CLUMP_MARK not in text:
            continue
        for name, content in unclump_text(text).items():
            q = os.path.join(root, "src", *name.split(".")) + ".lean"
            with open(q, "w", encoding="utf-8") as f:
                f.write(content)
        n += 1
    print(f"unclumped {n} files")


# ---------------------------------------------------------------------------

def blame(root, logs):
    """Map `error: <file>:<line>:...` lines in build logs to the clump member containing them."""
    err = re.compile(r"^error: (src/\S+?\.lean):(\d+):")
    found = set()
    for log in logs:
        with open(log, encoding="utf-8", errors="replace") as f:
            for l in f:
                m = err.match(l)
                if not m:
                    continue
                path, line = m.group(1), int(m.group(2))
                try:
                    with open(os.path.join(root, path), encoding="utf-8") as g:
                        lines = g.read().split("\n")[:line]
                except FileNotFoundError:
                    continue
                member = None
                for x in reversed(lines):
                    if x.startswith(SEAM_BEGIN):
                        member = x[len(SEAM_BEGIN):].rstrip(" =")
                        break
                if member:
                    found.add(member)
    return sorted(found)


def read_exclude(path):
    if not path or not os.path.exists(path):
        return frozenset()
    with open(path) as f:
        return frozenset(l.split("#")[0].strip() for l in f if l.split("#")[0].strip())


def stats(mods, clumps, max_lines):
    gone = sum(len(o) - 1 for o in clumps.values())
    print(f"modules {len(mods)}  clumps {len(clumps)}  absorbed {gone}  "
          f"files after {len(mods) - gone}  (max-lines {max_lines})")
    sizes = []
    in_clump = set()
    for r, o in clumps.items():
        in_clump.update(o)
        sizes.append(sum(mods[m].lines for m in o))
    sizes += [mods[m].lines for m in mods if m not in in_clump]
    bins = [0, 50, 100, 200, 500, 1000, 2000, 5000, 10000, 10**9]
    for a, b in zip(bins, bins[1:]):
        c = sum(a <= s < b for s in sizes)
        print(f"  {a:>6}-{b:<6} {c:7d}")


def main():
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="cmd", required=True)
    p = sub.add_parser("plan"); p.add_argument("root"); p.add_argument("--max-lines", type=int, default=10000)
    p.add_argument("--out")
    p.add_argument("--exclude", default=os.path.join(os.path.dirname(__file__), "clump-exclude.txt"),
                   help="modules never to fold (one per line; default scripts/clump-exclude.txt)")
    b = sub.add_parser("blame", help="list clump members containing errors in build logs")
    b.add_argument("root"); b.add_argument("logs", nargs="+")
    a = sub.add_parser("apply"); a.add_argument("root"); a.add_argument("plan")
    u = sub.add_parser("unclump"); u.add_argument("root")
    args = ap.parse_args()
    if args.cmd == "plan":
        mods = load(args.root)
        clumps = plan(mods, args.max_lines, read_exclude(args.exclude))
        stats(mods, clumps, args.max_lines)
        if args.out:
            with open(args.out, "w") as f:
                json.dump(clumps, f, indent=0)
    elif args.cmd == "apply":
        with open(args.plan) as f:
            apply(args.root, json.load(f))
    elif args.cmd == "blame":
        print("\n".join(blame(args.root, args.logs)))
    else:
        unclump(args.root)


if __name__ == "__main__":
    main()
