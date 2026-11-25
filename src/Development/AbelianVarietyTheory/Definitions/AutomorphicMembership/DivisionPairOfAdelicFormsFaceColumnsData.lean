module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Formalism.LocalToGlobal.IndefiniteReal.RealTB
public import Lean.Meta.Injective

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev

namespace GlobalTheory.Mem.R3

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {K : Formalism.MainNotions.G.Consts} {Yd : DivX D}
  {cX : ExtraC}


set_option genInjectivity false in
set_option genSizeOfSpec false in

structure TwIn (ex : Extra D L hT Gi Gl K Yd cX) : Type 1 where
  G : Type
  [grp : Group G]
  [fin : Fintype G]
  Pl0 : Type
  I0 : Type
  T : Type
  A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m
  core : Formalism.L2.Pj.CoreJ D
  [alg : Algebra core.Q.c.F D.what₂.LL]
  R : RealDat3 D A3 core.Q.c.F
  F : Face3 D A3
  cG : G0 R.Pg D.R.r ≃* G0g D.nd
  geo : GlobalTheory.RealGeo.GeoHalf core R.toRealDat fun _ => 1
  pins : Pins R F cG
  err : ErrEq R F
  Y : Read (A3 := A3) R.toRealDat F.lv2 ex.p0
  Z : ReadL R F ex.p0 Y
  C : ReadC R F ex.p0 Y
  sEE : (R.toCx3 F).EE →ₗ⋆[ℂ] (F.fc (R.toCx3 F).zs).Sp.HH
  div : DivDef3 D A3 F.P0 F.ψ0 F.P1 F.ψ1 (zsOf R F) (s0Of R F) (s1Of R F) ex.p0 (colOf R F sEE) C.NuC (idsOf cG Z C)
  JM : MjHIds D A3.A Yd (A3.indefDown (s0Of R F))
  mjH : MjHTie D A3.A Yd (A3.indefDown (s0Of R F)) Z.jW JM

attribute [instance] TwIn.grp TwIn.fin TwIn.alg

variable {ex : Extra D L hT Gi Gl K Yd cX}



@[reducible] def divisionPairOfAdelicFormsFaceColumnsData (x : TwIn ex) : RowSideFamily ex where
  Gp := x.G
  Pl0 := x.Pl0
  I0 := x.I0
  T := x.T
  A3 := x.A3
  P0 := x.F.P0
  ψ0 := x.F.ψ0
  Ps := x.F.P1
  ψs := x.F.ψ1
  Zs := zsOf x.R x.F
  S0 := s0Of x.R x.F
  S1 := s1Of x.R x.F
  Dc := x.F.Dc (zsOf x.R x.F)
  Sp := x.F.Sp (zsOf x.R x.F)
  C := colOf x.R x.F x.sEE
  NuC := x.C.NuC
  I := idsOf x.cG x.Z x.C
  JM := x.JM
  tied := ⟨x.div, x.mjH, x.Y.cen0 x.cG x.pins.keep⟩

def TwIn.wd (x : TwIn ex) : (x.F.Dc (zsOf x.R x.F)).Mem → D.what₂.Word := (Equiv.ofBijective _ x.C.bij).symm

theorem TwIn.wd_wU (x : TwIn ex) (u : D.what₂.Word) : x.wd (x.C.wU u) = u := (Equiv.ofBijective _ x.C.bij).symm_apply_apply u

theorem TwIn.wU_wd (x : TwIn ex) (m : (x.F.Dc (zsOf x.R x.F)).Mem) : x.C.wU (x.wd m) = m :=
  (Equiv.ofBijective _ x.C.bij).apply_symm_apply m

def TwIn.bR (x : TwIn ex) (m : (x.F.Dc (zsOf x.R x.F)).Mem) (i : Fin ((x.F.Dc (zsOf x.R x.F)).a m)) : (D.mem (x.wd m)).A.Mram :=
  D.eMu (x.wd m) (D.jN (x.wd m) (x.C.eNu (x.wd m)
    (Pi.single (Fin.cast (congrArg (x.F.Dc (zsOf x.R x.F)).a (x.wU_wd m)).symm i) 1)))


set_option genInjectivity false in
set_option genSizeOfSpec false in

structure RealIn (x : TwIn ex) (Rc : Formalism.L2.RecT ex) (S : Formalism.L2.SG.SpectralTiesReal.STiesR Rc) : Type 1 where
  psiPin : x.R.ψ = Rc.T.theta.W.ψ
  hin : ∀ u, Formalism.L2.SG.PoincareInHH.PoincareSetting.InHH S.X u S.Y.hK
  spPin : HEq (x.F.Sp (zsOf x.R x.F)) (Formalism.IndefR.Cx.spOf (X := S.X) (twAt D.what₂.embLL x.A3.A.v0) (x.F.Dc (zsOf x.R x.F)) S.Y.hK S.G
    x.wd (fun m => pwOf S hin (x.wd m)) x.bR)
  Sx : Formalism.IndefR.NX.RatDat D.ntw
  nexp : Formalism.IndefR.NX.NExpRealS x.R x.cG Sx
  stdV : ∀ i, (∀ a b, (Vc D i).hT ((Vc D i).frame a) ((Vc D i).frame b) = if a = b then 1 else 0) ∧
    (Vc D i).L0 = Submodule.span (𝓞 D.host.E) (Set.range (Vc D i).frame)
  stdX : (∀ a b, D.sp.X'.hT (D.sp.X'.frame a) (D.sp.X'.frame b) = if a = b then 1 else 0) ∧
    D.sp.X'.L0 = Submodule.span (𝓞 D.host.E) (Set.range D.sp.X'.frame)
  tS : Formalism.L2.Theta.GA D (Yc D 0)
  cS : ℝ
  κS : ℝ
  ιS : Formalism.L2.Theta.GA D (Yc D 0) ≃* S.X.B.I.GA
  instEq : S.X.B.I = Formalism.IndefR.RationalEmbedding.inst D
  ιS_eq : HEq ιS (Formalism.IndefR.RationalEmbedding.iota D).toMulEquiv
  sEEc : Tw (twAt D.what₂.embLL x.A3.A.v0) x.R.HE.H →ₗ⋆[ℂ] Tw (twAt D.what₂.embLL x.A3.A.v0) (Formalism.L2.SG.PoincareInHH.PoincareSetting.HHX S.X)
  sEEj : HEq x.sEE sEEc
  seeLev : (∃ t' : Formalism.L2.Theta.GA D (Yc D 0), Formalism.IndefR.AutomorphicEvaluation.ConjLevel t'⁻¹ (levS _ (x.R.βY 0) (x.R.dat0 (x.R.toRealDat.levR x.F.lv2 true))) (Formalism.IndefR.Lev.levChi _ (x.R.βY 0) (x.R.dat0 (x.R.toRealDat.levR x.F.lv2 true))) (ιS ⁻¹' seeKS S.X) (fun k => seeChiS S.X (ιS k))) →
    Formalism.IndefR.AutomorphicEvaluation.ConjLevel tS⁻¹ (levS _ (x.R.βY 0) (x.R.dat0 (x.R.toRealDat.levR x.F.lv2 true))) (Formalism.IndefR.Lev.levChi _ (x.R.βY 0) (x.R.dat0 (x.R.toRealDat.levR x.F.lv2 true))) (ιS ⁻¹' seeKS S.X) (fun k => seeChiS S.X (ιS k))
  seeEval : (∃ c' : ℝ, Formalism.IndefR.AutomorphicEvaluation.EvalTieT (x.R.MY 0) x.R.ν0 x.R.fd0 (x.R.toRealDat.EEat (x.R.toRealDat.levR x.F.lv2 true)) S.X S.G ιS tS c') →
    Formalism.IndefR.AutomorphicEvaluation.EvalTieT (x.R.MY 0) x.R.ν0 x.R.fd0 (x.R.toRealDat.EEat (x.R.toRealDat.levR x.F.lv2 true)) S.X S.G ιS tS cS
  uS : ℂ
  uS_norm : ‖uS‖ = 1
  seeDef : ∀ (v : Tw (twAt D.what₂.embLL x.A3.A.v0) x.R.HE.H) (hx : x.R.HE.e (Tw.out v) ∈ (x.R.toRealDat.EEat (x.R.toRealDat.levR x.F.lv2 true))),
    sEEc v = Tw.mk (twAt D.what₂.embLL x.A3.A.v0) ((uS * (κS : ℂ)) • (Formalism.IndefR.AutomorphicEvaluation.sEEofTT (x.R.MY 0) x.R.ν0 x.R.fd0 (x.R.toRealDat.EEat (x.R.toRealDat.levR x.F.lv2 true)) S.X S.G ιS tS cS) ⟨x.R.HE.e (Tw.out v), hx⟩)
  seeK : 0 < κS ∧ ((∃ κ' : ℝ, 0 < κ' ∧ ∀ (v : Tw (twAt D.what₂.embLL x.A3.A.v0) x.R.HE.H) (hx : x.R.HE.e (Tw.out v) ∈ (x.R.toRealDat.EEat (x.R.toRealDat.levR x.F.lv2 true))),
      ‖(κ' : ℂ) • (Formalism.IndefR.AutomorphicEvaluation.sEEofTT (x.R.MY 0) x.R.ν0 x.R.fd0 (x.R.toRealDat.EEat (x.R.toRealDat.levR x.F.lv2 true)) S.X S.G ιS tS cS) ⟨x.R.HE.e (Tw.out v), hx⟩‖ = ‖v‖) →
    ∀ (v : Tw (twAt D.what₂.embLL x.A3.A.v0) x.R.HE.H), x.R.HE.e (Tw.out v) ∈ (x.R.toRealDat.EEat (x.R.toRealDat.levR x.F.lv2 true)) →
      RealDat.nP x.F.lv2 true * ‖sEEc v‖ ^ 2 = ‖v‖ ^ 2)
  host : HostHyp D
  vpos : ∀ i, (Vc D i).IsPosDef

variable {x : TwIn ex} {Rc : Formalism.L2.RecT ex} {S : Formalism.L2.SG.SpectralTiesReal.STiesR Rc}


theorem phEff_one (x : TwIn ex) : phEff x.R = fun _ => 1 := by
  funext i
  unfold phEff
  rw [x.pins.phs i]
  simp




end GlobalTheory.Mem.R3

end
