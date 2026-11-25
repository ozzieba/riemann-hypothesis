module

public import Formalism.LocalToGlobal.Divisibility.Frames
public import Formalism.LocalToGlobal.Divisibility.FramesLemmas

@[expose] public section

open NumberField
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory.AmbCrd

open Formalism.L2.DIV

section Frames

variable {K : Type} [Field K] [NumberField K]


open Classical in
def frm {n : ℕ} (H : Matrix (Fin n) (Fin n) K) : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ :=
  fun v => if (H.map v.embedding).PosDef then frameOf (H.map v.embedding) else 1

theorem frm_det {n : ℕ} (H : Matrix (Fin n) (Fin n) K) (v : InfinitePlace K) : IsUnit (frm H v).det := by
  unfold frm
  split_ifs with h
  · exact (frameOfSpec _ _ h).1
  · simp

theorem frm_of_posDef {n : ℕ} (H : Matrix (Fin n) (Fin n) K) (v : InfinitePlace K) (h : (H.map v.embedding).PosDef) :
    frm H v = frameOf (H.map v.embedding) := by
  unfold frm
  rw [ite_eq_left h]

end Frames

end GlobalTheory.AmbCrd

end
