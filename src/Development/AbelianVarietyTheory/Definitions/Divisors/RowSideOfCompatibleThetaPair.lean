module

public import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT

open GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.BigTop

namespace GlobalTheory.Fc.Ind

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX}

@[reducible] def rowSideOfCompatibleThetaPair (P : RowSideFamily ex) : IndefiniteRowSideFullHecke ex where
  Gp := P.Gp
  Pl0 := P.Pl0
  I0 := P.I0
  T := P.T
  A3 := P.A3
  P0 := P.P0
  ψ0 := P.ψ0
  Ps := P.Ps
  ψs := P.ψs
  Zs := P.Zs
  S0 := P.S0
  S1 := P.S1
  Dc := P.Dc
  Sp := P.Sp
  C := P.C
  NuC := P.NuC
  I := P.I
  JM := P.JM
  div := P.tied.div
  mjH := P.tied.mjH
  cen0 := P.tied.cen0

abbrev zscOf (P : RowSideFamily ex) (Del h0 : ℕ) (c : ℝ) : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3 :=
  (rowSideOfCompatibleThetaPair P).zsc Del h0 c

abbrev PtP : Type 1 := ∀ (D : D7) (O : Obj D) (c : ℝ), PtAt O.ex c → Prop

end GlobalTheory.Fc.Ind

end
