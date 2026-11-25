module

public import Formalism.LocalToGlobal.HilbertRowConditions.RowPin
public import Formalism.LocalToGlobal.Divisibility.DivisionCompatibleToSub2Indef2
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain

namespace Formalism.L2.Rows

open Formalism.L2.DIV Formalism.L2.Indef

section Joint

variable (D : D7) {Gp : Type} [Group Gp] [Fintype Gp] {Pl0 I0 Ty T : Type}
  (A3 : FamIn3 D.what₂.LL Gp Pl0 I0 Ty T D.R.m)

structure BaseDivisionAmbientCompatibilityFamily (Y : DivX D) (p0 : BaseLevelRowSide D)
    (P0 : Subgroup Gp) (ψ0 : P0 →* D.what₂.LLˣ) (Ps : Subgroup Gp) (ψs : Ps →* D.what₂.LLˣ)
    (Zs : DefSub A3.fam3.amb3) (S0 : IndefData (A3.side3 P0 ψ0 Zs)) (S1 : IndefData (A3.side3 Ps ψs Zs))
    {Dc : DefCols (A3.side3 Ps ψs Zs)} {Sp : SPer Dc} (C : ColData Dc Sp S1)
    (NuC : ∀ u, Submodule (𝓞 D.what₂.LL) (Fin (Dc.a u) → D.what₂.LL))
    (I : DivisionCompatibilityDataThreeSided D A3 P0 ψ0 Ps ψs Zs S0 S1 p0 Dc)
    (JM : MjHIds D A3.A Y (A3.indefDown S0)) : Prop where

  div : DivDef3 D A3 P0 ψ0 Ps ψs Zs S0 S1 p0 C NuC I

  mjH : MjHTie D A3.A Y (A3.indefDown S0) I.jW JM

  cen0 : CenTie D A3.A p0.s P0 ψ0 I.eG I.tup I.jA0

end Joint

section Bundle

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {Kc : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC}

structure RowSideFamily (ex : Extra D L hT Gi Gl Kc Y cX) : Type 1 where
  Gp : Type
  [grp : Group Gp]
  [fin : Fintype Gp]
  Pl0 : Type
  I0 : Type
  T : Type

  A3 : FamIn3 D.what₂.LL Gp Pl0 I0 (List ℕ) T D.R.m
  P0 : Subgroup Gp
  ψ0 : P0 →* D.what₂.LLˣ
  Ps : Subgroup Gp
  ψs : Ps →* D.what₂.LLˣ
  Zs : DefSub A3.fam3.amb3
  S0 : IndefData (A3.side3 P0 ψ0 Zs)
  S1 : IndefData (A3.side3 Ps ψs Zs)
  Dc : DefCols (A3.side3 Ps ψs Zs)
  Sp : SPer Dc
  C : ColData Dc Sp S1
  NuC : ∀ u, Submodule (𝓞 D.what₂.LL) (Fin (Dc.a u) → D.what₂.LL)
  I : DivisionCompatibilityDataThreeSided D A3 P0 ψ0 Ps ψs Zs S0 S1 ex.p0 Dc
  JM : MjHIds D A3.A Y (A3.indefDown S0)
  tied : BaseDivisionAmbientCompatibilityFamily D A3 Y ex.p0 P0 ψ0 Ps ψs Zs S0 S1 C NuC I JM

attribute [instance] RowSideFamily.grp RowSideFamily.fin

variable {ex : Extra D L hT Gi Gl Kc Y cX}


open Classical in
structure RowSideDetermined (T : TiedDataSK ex) (P : RowSideFamily ex) : Prop where

  lowerMap : ∀ u, LowerMapTieS (T.cols.forms u)

  lowerMapTw : ∀ u μ (hμ : μ ≠ D.what₂.mu0) (_hw : ∃ w, μ = D.what₂.muAt w) (h1 : 1 ≤ D.R.m), LowerMapTieTw T u μ hμ h1

  buDef : Formalism.BasicNotions.Rows.BuDefQ D.what₂

  faces : ∃ (Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)) (Spf : ∀ Zs, SPer (Dcf Zs)),
    Dcf P.Zs = P.Dc ∧ HEq (Spf P.Zs) P.Sp

  gamDvd : (∀ (t : P.T) (c : (P.A3.A.fam.R t).S.Cl), Fintype.card ((P.A3.A.fam.R t).S.Gam c) ∣ (D.mem D.u₀).C.DGam) ∧
    ∀ (j : Fin D.R.m) (t : P.T) (c : (P.A3.A.fam.L j t).S.Cl), Fintype.card ((P.A3.A.fam.L j t).S.Gam c) ∣ (D.mem D.u₀).C.DGam

structure RowsHold0_3 (P : RowSideFamily ex) : Prop where
  zsSt : P.Zs.Stable
  zsBl : P.Zs.InBlock
  rows0 : ∃ R0 : IndefRows (P.A3.side3 P.P0 P.ψ0 P.Zs), R0.toIndefData = P.S0
  famOk : ∃ s, P.A3.fam3.Ok3 s
  famSep : P.A3.fam3.TypesSep3

def RowsHoldKap3 (P : RowSideFamily ex) : Prop := ∀ e : D.what₂.LL →+* ℂ, Y.kapR e = P.S1.κ (InfinitePlace.mk e)


open Classical in
def RowsHoldLam3 (P : RowSideFamily ex) : Prop :=
  ∃ cOf : D.what₂.FT → P.A3.fam3.base3.Ix,
    (∀ (i : Fin D.R.m) (c : P.A3.fam3.base3.Ix),
      iSupIndep (fun σ : {σ : D.what₂.FT // cOf σ = c} => D.what₂.isot ((i : ℕ) + 1) σ.1) ∧
      (⨆ σ : {σ : D.what₂.FT // cOf σ = c}, D.what₂.isot ((i : ℕ) + 1) σ.1) =
        Submodule.span ℂ ((P.I.jW i) '' (P.S0.Wp i c : Set (Fin (P.S0.dW i) → D.what₂.LL)))) ∧
    (∀ (i : Fin D.R.m) (t : P.T) (σ : D.what₂.FT),
      (P.I.tup t = D.what₂.mu0 ∨ ∃ w, P.I.tup t = D.what₂.muAt w) → D.what₂.isot ((i : ℕ) + 1) σ ≠ ⊥ →
      D.what₂.lamP (P.I.tup t) ((i : ℕ) + 1) σ = P.S0.lam i t (cOf σ) P.A3.fam3.base3.v0) ∧
    (∀ c : P.A3.fam3.base3.Ix,
      ∑ σ ∈ Finset.univ.filter (fun σ => cOf σ = c), D.what₂.nRows0 σ = Module.finrank D.what₂.LL (P.S0.Ep c))

def RowsHoldDcPt3 (P : RowSideFamily ex) : Prop :=
  ∀ (u : D.what₂.Word) (t : P.T) (x : Fin (P.Dc.a (P.I.wU u)) → D.what₂.LL)
    (F : Fin ((P.A3.side3 P.Ps P.ψs P.Zs).nV t) → D.what₂.LL),
    D.what₂.embLL (P.Dc.Pt (P.I.wU u) t x F) =
      D.what₂.perCol u (P.I.tup t) (D.jN u (P.I.eNu u x)) (P.I.jA t ((rV0 D P.A3.A P.Ps P.ψs t).mulVec F))

end Bundle

end Formalism.L2.Rows

end
