module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TwArgs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PlaceModelImp

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.Mem.R3

theorem twArgs_lev : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl) (L : SizeData₂ (w.st Z).toD7) (hT : GatTies (w.st Z).toD7) (Gi : Formalism.MainNotions.G.Inst (w.st Z).toD7 L) (Gl : Formalism.MainNotions.G.LatInst (w.st Z).toD7) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX (w.st Z).toD7) (cX : ExtraC) (ex : Extra (w.st Z).toD7 L hT Gi Gl Kc Yd cX) (t : RowsT K w Z Wt ex.p0) (a : TwArgs ex t), HEq a.x.R.C (Top.Fr.at (w.st Z) f) ∧ HEq a.x.R.Pg (B.primes w.px).vGs ∧ (∀ μ, Formalism.IndefR.RecTie.Used0 (w.st Z).toD7 μ → HEq (a.x.R.Q (a.x.Y.tupT μ)) (w.I.Q μ) ∧ HEq (a.x.R.toLevCh.xiH (a.x.Y.tupT μ)) (w.I.xi μ)) ∧ (∀ i p v s, a.x.R.EEp3 p ≠ ⊥ → ∃ p' s', HEq p' p ∧ HEq s' s ∧ a.x.R.lam3 i s p v = t.r.z.R.lam3 i s' p' v) := by
  intro K B f T w Z Wt L hT Gi Gl Kc Yd cX ex t a
  cases a with
  | mk Dc Sp Zsc lam err lam_eq x pack intersectionNumber_baseChange hκ hv hfw htup htupT hjA hjA0 heMt hPY hPW heFT hIL heE heW hjW heRR =>
  cases x with
  | mk G Pl0 I0 T' A3 core R F cG geo pins err' Y Z' C' sEE div JM mjH =>
  cases pack
  have hT' : Y.tupT = t.r.Y.tupT := eq_of_heq htupT
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact heq_of_eq (t.r.z.lev.C.trans (congrArg _ w.C_eq))
  · exact heq_of_eq t.r.z.lev.Pg
  · change ∀ μ, Formalism.IndefR.RecTie.Used0 (w.st Z).toD7 μ →
      HEq (t.r.z.R.Q (Y.tupT μ)) (w.I.Q μ) ∧ HEq (t.r.z.R.xiH (Y.tupT μ)) (w.I.xi μ)
    intro μ hμ
    have hix : ixOf w.I (usedOf w.I T Wt) (t.r.Y.tupT μ) = μ := (t.r.tup_ix _).symm.trans (t.r.Y.tupTie μ hμ)
    rw [hT', t.r.z.lev.Q, t.r.z.lev.xiH, hix]
    exact ⟨HEq.rfl, HEq.rfl⟩
  · intro i p v s hp
    refine ⟨p, s, HEq.rfl, HEq.rfl, ?_⟩
    change t.r.z.R.EEp3 p ≠ ⊥ at hp
    change lam i s p v = t.r.z.R.lam3 i s p v
    exact lam_eq i s p v hp


end GlobalTheory.Mem.R3
