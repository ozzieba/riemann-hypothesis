module

public import Formalism.LocalToGlobal.Divisibility.PsiWeilOfAbsNorm
public import Formalism.LocalToGlobal.Divisibility.NumericScaleExponentEqExtended
public import Formalism.LocalToGlobal.Divisibility.NumbersLemmas
public import Formalism.SharpRestriction.PageFix
public import Formalism.SharpRestriction.SmoothDesignExistence.DGamSmooth
public import Formalism.SharpRestriction.Divisibility.SmallFirstModulusBelowScale
public import Formalism.SharpRestriction.LevelLetterCocycles.AlignN
public import Formalism.SharpRestriction.GlobalSchurBounds.WeightVectorSmallSharesEight
public import Formalism.LocalToGlobal.IndefiniteReal.RealTB
public import Formalism.LocalToGlobal.IndefiniteReal.RealRecPins
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsDeltaDelAtOwnAt
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsScalar
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.FamilyClassSevenDutiesAndStableLattices
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.RationalRayLevels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DimPartsAtIffBadAndOff
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RayFieldTheta
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

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT

namespace GlobalTheory.BigTop

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC}


set_option genInjectivity false in
set_option genSizeOfSpec false in
structure IndefiniteRowSideFullHecke (ex : Extra D L hT Gi Gl Kc Y cX) : Type 1 where

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

  div : DivDef3 D A3 P0 ψ0 Ps ψs Zs S0 S1 ex.p0 C NuC I

  mjH : MjHTie D A3.A Y (A3.indefDown S0) I.jW JM

  cen0 : CenTie D A3.A ex.p0.s P0 ψ0 I.eG I.tup I.jA0

attribute [instance] IndefiniteRowSideFullHecke.grp IndefiniteRowSideFullHecke.fin

variable {ex : Extra D L hT Gi Gl Kc Y cX}

abbrev IndefiniteRowSideFullHecke.toRowSideFamily (P : IndefiniteRowSideFullHecke ex) : RowSideFamily ex :=
  { Gp := P.Gp, Pl0 := P.Pl0, I0 := P.I0, T := P.T, A3 := P.A3, P0 := P.P0, ψ0 := P.ψ0, Ps := P.Ps, ψs := P.ψs, Zs := P.Zs,
    S0 := P.S0, S1 := P.S1, Dc := P.Dc, Sp := P.Sp, C := P.C, NuC := P.NuC, I := P.I, JM := P.JM,
    tied := ⟨P.div, P.mjH, P.cen0⟩ }

def IndefiniteRowSideFullHecke.zsc (P : IndefiniteRowSideFullHecke ex) (Del h0 : ℕ) (Csz : ℝ) : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3 :=
  fun Zs =>
    let z := ZscOfNum3 P.A3 P.P0 P.ψ0 (ofRecord D L Del h0) (Equiv.refl _) L.Nc Zs
    { z with l6m := fun j => z.l6m j - Csz * z.l6u, l6u := 0 }

def IndefiniteRowSideFullHecke.face (P : IndefiniteRowSideFullHecke ex) (Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs))
    (Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)) (Del h0 : ℕ) (Csz : ℝ) : Face3 D P.A3 :=
  ⟨P.P0, P.ψ0, P.Ps, P.ψs, Dcf, Spf, P.zsc Del h0 Csz⟩

export Formalism.IndefR (errCan phEff)


open Classical in
set_option genInjectivity false in
set_option genSizeOfSpec false in
structure PtAt (ex : Extra D L hT Gi Gl Kc Y cX) (Csz : ℝ) : Type 1 where

  P : IndefiniteRowSideFullHecke ex

  Del : ℕ

  h0 : ℕ

  hDel : D.s.Del = (Del : ℚ)

  hh0 : L.etaSz = (D.R.m : ℝ) * (h0 : ℝ)

  Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)

  Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)

  gamDvd : (∀ (t : P.T) (c : (P.A3.A.fam.R t).S.Cl), Fintype.card ((P.A3.A.fam.R t).S.Gam c) ∣ (D.mem D.u₀).C.DGam) ∧
    ∀ (j : Fin D.R.m) (t : P.T) (c : (P.A3.A.fam.L j t).S.Cl), Fintype.card ((P.A3.A.fam.L j t).S.Gam c) ∣ (D.mem D.u₀).C.DGam

  T : CoreJ D
  [alg : Algebra T.Q.c.F D.what₂.LL]

  R : RealDat3 D P.A3 T.Q.c.F

  charW : R.WeakCharacterisation (P.face Dcf Spf Del h0 Csz)

  zs : (R.toCx3 (P.face Dcf Spf Del h0 Csz)).zs = P.Zs

  s0 : HEq ((R.toCx3 (P.face Dcf Spf Del h0 Csz)).data (P.face Dcf Spf Del h0 Csz).cr false) P.S0

  s1 : HEq ((R.toCx3 (P.face Dcf Spf Del h0 Csz)).data (P.face Dcf Spf Del h0 Csz).cr true) P.S1

  dc : Dcf P.Zs = P.Dc

  stdChar : Formalism.L2.Theta.IsStdChar D R.ψ (-1)

  signs : Formalism.IndefR.Mi.SignsAtG R.toRealDat (P.face Dcf Spf Del h0 Csz).lv2

  cG : Formalism.L2.DIV.G0 R.Pg D.R.r ≃* G0g D.nd

  Sx : Formalism.IndefR.NX.RatDat D.ntw

  nexp : Formalism.IndefR.NX.NExpRealS R cG Sx

  stdV : ∀ i, (∀ a b, (Vc D i).hT ((Vc D i).frame a) ((Vc D i).frame b) = if a = b then 1 else 0) ∧
    (Vc D i).L0 = Submodule.span (𝓞 D.host.E) (Set.range (Vc D i).frame)

  stdX : (∀ a b, D.sp.X'.hT (D.sp.X'.frame a) (D.sp.X'.frame b) = if a = b then 1 else 0) ∧
    D.sp.X'.L0 = Submodule.span (𝓞 D.host.E) (Set.range D.sp.X'.frame)

  host : HostHyp D

  err_eq : ∀ w j, ((R.toCx3 (P.face Dcf Spf Del h0 Csz)).data (P.face Dcf Spf Del h0 Csz).cr false).err0 w j =
    errCan ((R.toCx3 (P.face Dcf Spf Del h0 Csz)).data (P.face Dcf Spf Del h0 Csz).cr false)
      ((P.face Dcf Spf Del h0 Csz).fc (R.toCx3 (P.face Dcf Spf Del h0 Csz)).zs).Z.F0 w

  vpos : ∀ i, (Vc D i).IsPosDef

  κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)

  v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.toRealDat.MW i σ).Vec

  fw : FWTie T R.toRealDat κ v₀

  bar : BarTie fw

  O : ∀ i, OMDat T.toCore R.toRealDat i Unit (fun _ => P.A3.A.μ0)

  pins : ∀ i, OMPins T R.toRealDat κ v₀ O i

  rhoGeo : RhoGeo fw O

  equivAll : EquivAll T R.toRealDat κ O

  cTie : ∀ i, CTie T R.toRealDat κ v₀ O i

  phase : ∀ i, R.toRealDat.LUnif → PhaseTie T R.toRealDat κ v₀ O (phEff R) i

  qGuard : QGuard R.toRealDat

  hF : D.host.F = maximalRealSubfield D.host.E

  phsOne : ∀ i, R.phs i = 1

  prXunit : Formalism.IndefR.Seed.PrIso R.MX R.cX R.prX

  grpRecPin : ∃ (plg : (Σ k : Fin 2, D.nd.PlG k) ≃ R.toRealDat.Pg)
      (iso : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ZMod (D.host.g kv.1) ≃+* kP (plg kv).1),
    (∀ kv, ((plg kv : R.toRealDat.Pg) : Pl D.host.E) = D.naut.plGw kv.1 kv.2) ∧
    (∀ g, D.what₂.embLL ((idemOf P.A3.A.X).coeff g) = D.ntypes.e0.coeff ((R.eG.trans cG) g)) ∧
    (∀ kv, R.toRealDat.C.P.Div kv.1 (plg kv).1) ∧
    ∀ g kv, R.toRealDat.eG g (plg kv) = Formalism.UG.bc (iso kv : ZMod (D.host.g kv.1) →+* kP (plg kv).1) ((R.eG.trans cG) g kv)

  fdiag : ∀ i, IsFDiag (Wc D i) ∧ IsFDiag (Vc D i)

  eGtie : P.I.eG = R.eG.trans cG

  betaStd : (∀ i, R.βV i = 1) ∧ R.βX = 1

  tupT : D.what₂.Tup → P.T

  hm : 0 < D.R.m

  Tp : Formalism.L2.Host.TupTied D R.C ex.nch

  tupXi : ∀ μ, (μ = D.what₂.mu0 ∨ ∃ w, μ = D.what₂.muAt w) → R.toRealDat.toLevCh.xiH (tupT μ) = Tp.xi μ

  tupAt : ∀ w, tupT (D.what₂.muAt w) = R.mu (D.plEq w)

  tupTie : ∀ μ, (μ = D.what₂.mu0 ∨ ∃ w, μ = D.what₂.muAt w) → P.I.tup (tupT μ) = μ

  tupT_tup : ∀ t, tupT (P.I.tup t) = t

  muEq : R.mu = P.S0.μ

attribute [instance] PtAt.alg

namespace PtAt

variable {Csz : ℝ}



def ofReal (P : IndefiniteRowSideFullHecke ex) (Del h0 : ℕ) (hDel : D.s.Del = (Del : ℚ)) (hh0 : L.etaSz = (D.R.m : ℝ) * (h0 : ℝ))
    (Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)) (Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs))
    (gamDvd : (∀ (t : P.T) (c : (P.A3.A.fam.R t).S.Cl), Fintype.card ((P.A3.A.fam.R t).S.Gam c) ∣ (D.mem D.u₀).C.DGam) ∧
      ∀ (j : Fin D.R.m) (t : P.T) (c : (P.A3.A.fam.L j t).S.Cl), Fintype.card ((P.A3.A.fam.L j t).S.Gam c) ∣ (D.mem D.u₀).C.DGam)
    {Rc : RecT ex} {S : Formalism.L2.SG.SpectralTiesReal.STiesR Rc} (B : RealTB Rc P.toRowSideFamily Dcf Spf (P.zsc Del h0 Csz) S)
    (Qp : RealPins B.Q) (Qr : RealRec B.Q) : PtAt ex Csz :=
  { P := P, Del := Del, h0 := h0, hDel := hDel, hh0 := hh0, Dcf := Dcf, Spf := Spf, gamDvd := gamDvd
    T := B.T, alg := B.alg, R := B.Q.Rl
    charW := B.Q.charW, zs := B.Q.zs, s0 := B.Q.s0, s1 := B.Q.s1, dc := B.Q.dc, stdChar := B.Q.stdChar, signs := B.Q.signs
    cG := B.Q.cG, Sx := B.Q.Sx, nexp := B.Q.nexp, stdV := B.Q.stdV, stdX := B.Q.stdX, host := B.Q.host, err_eq := B.Q.err_eq
    vpos := B.Q.vpos
    κ := B.κ, v₀ := B.v₀, fw := B.fw, bar := B.bar, O := B.O, pins := B.pins, rhoGeo := B.rhoGeo, equivAll := B.equivAll
    cTie := B.cTie, phase := B.phase
    qGuard := Qp.qGuard, hF := Qp.hF, phsOne := Qp.phsOne, prXunit := Qp.prXunit, grpRecPin := Qp.grpRecPin, fdiag := Qp.fdiag
    eGtie := Qp.eGtie, betaStd := Qp.betaStd
    tupT := Qr.tupT, hm := Qr.hm, Tp := Qr.Tp, tupXi := Qr.recR.tupXi, tupAt := Qr.recR.tupAt, tupTie := Qr.tupTie
    tupT_tup := Qr.tupT_tup, muEq := Qr.muEq }

variable (p : PtAt ex Csz)

abbrev F : Face3 D p.P.A3 := p.P.face p.Dcf p.Spf p.Del p.h0 Csz

abbrev S (b : Bool) := (p.R.toCx3 p.F).data p.F.cr b

abbrev Z : IndefScale p.P.A3.fam3.base3 := (p.F.fc (p.R.toCx3 p.F).zs).Z

abbrev N (C CH : ℝ) : IndefNum p.P.A3.fam3.base3 := p.R.num p.F C CH



def ExportRow : Prop :=
  ∃ jD : ∀ j, (Y.MjH j).V →ₗ[D.what₂.LL] p.Sx.WL j,
    (∀ (i : Fin D.R.m) (x : (Y.MjH ((i : ℕ) + 1)).V)
      (y : Fin (Module.finrank D.what₂.LL (p.R.toRealDat.WL p.F.lv2 false i)) → D.what₂.LL),
      HEq ((p.P.JM.eW i).symm x) y → (p.nexp.fi i).e (jD ((i : ℕ) + 1) x) = Formalism.IndefR.NX.jDL p.R p.F.lv2 i y) ∧
    Nonempty (Formalism.IndefR.NX.NMjR Y ex.nch)

def Realised : Prop :=
  ∃ (Rc : RecT ex) (S : Formalism.L2.SG.SpectralTiesReal.STiesR Rc)
    (B : RealTB Rc p.P.toRowSideFamily p.Dcf p.Spf (p.P.zsc p.Del p.h0 Csz) S) (Qp : RealPins B.Q) (Qr : RealRec B.Q),
    RealRecPins Qp Qr ∧ ofReal p.P p.Del p.h0 p.hDel p.hh0 p.Dcf p.Spf p.gamDvd B Qp Qr = p

def LevelTie : Prop :=
  (∀ g, (p.R.eG.trans p.cG) g ∈ D.nexp.U ↔ g ∈ p.P.P0) ∧
    ∀ (i : D.ntw.Tw) (b : Bool) (u : p.P.P0) (h : (p.R.eG.trans p.cG) u ∈ D.nexp.U), ∃ x : D.LL0,
      (x : D.what₂.LL) = (p.P.ψ0⁻¹ u : D.what₂.LLˣ) ∧
        ((D.nexp.psiU i b ⟨(p.R.eG.trans p.cG) u, h⟩ : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) =
          GlobalTheory.SeriesTie.sideEmb D.ntw i b x

def DataTie (_p : PtAt ex Csz) : Prop :=
  ∀ (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (a : D.nexp.Dat i ((j : ℕ) + 1) b),
    (∀ u : D.nexp.U, D.nexp.actG i _ b u (D.nexp.th i _ b a) =
      ((D.nexp.psiU i b u : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) • D.nexp.th i _ b a) → a ∈ ex.xd.xd0 i _ b

structure Ties : Prop where

  real : p.Realised

  core : GlobalTheory.BigOn.CoreTies L ex.errX p.T p.R.toRealDat

  pb : p.T.pb = p.R.C.P.pb

  types : GlobalTheory.DimPartsCompare.TameTie D p.R.C.W.om

  series : Nonempty (GlobalTheory.SeriesTie.ExportTie p.nexp p.v₀)

  level : p.LevelTie

  data : p.DataTie

  psiVal : ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → (p.Tp.psi w).ValuesIn 0 D.what₂.embLL

  ray : GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.RayIn D (D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde') (Formalism.L2.Host.embLL0 D).fieldRange

  roots : ∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (Formalism.L2.Host.embLL0 D).fieldRange

  rayQ : ∀ t, GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.ContainsRayField (GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.embK D) (GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.tupLevel p.R.toRealDat t)

  twist : GlobalTheory.EX.DQ.TwAllAt D ex.nch ex.xd

structure Rows : Prop where

  exAt : p.R.toRealDat.ExAt

  jEvBar : JEvBar p.T p.R.toRealDat p.κ

  geoAct : GeoAct p.T p.R.toRealDat p.κ p.v₀

  evInj : EvInj p.T p.R.toRealDat p.v₀

  ioExt : IoExt p.R.toRealDat

  oneMap : ∀ i, OneMapRowR p.T p.R.toRealDat p.κ p.v₀ p.O (phEff p.R) i

  prim : PrimRows3 p.R p.F

  sep : p.P.A3.fam3.TypesSep3

  ok : p.P.A3.fam3.Ok3 1

  framesOK : Formalism.IndefR.Mi.FramesOKg2 p.R

  divRows : DivRows3 D p.P.A3 p.P.P0 p.P.ψ0 p.P.Ps p.P.ψs p.P.Zs p.P.S0 p.P.S1 ex.p0 p.P.C p.P.NuC p.P.I

  psi : PsiPPTie D p.P.P0 p.P.ψ0 p.P.Ps p.P.ψs p.P.I.eG

  d0 : D.what₂.D0 = (p.P.A3.A.fam.R p.P.A3.A.fam.μ0).dZ (p.P.A3.A.fam.lvl p.P.P0 p.P.ψ0) (p.P.Zs.Z p.P.A3.A.fam.μ0)

  export_ : p.ExportRow

  goodFT : Formalism.BasicNotions.GoodFTAll D

  w1 : ∀ w, (p.R.toCx3 p.F).W1 p.F.cr (p.N 0 0) w → w ∈ p.R.twPl

  ties : p.Ties

theorem phEff_one (i : Fin D.R.m) : phEff p.R i = 1 := by
  unfold phEff
  rw [p.phsOne i, map_one]

theorem tupleRead_baseTuple_eq_family : p.tupT D.what₂.mu0 = p.P.A3.A.μ0 :=
  p.charW.base.lev.xi_inj (by rw [p.tupXi D.what₂.mu0 (Or.inl rfl), p.Tp.trueColumnChoices_heckeChar_reference_eq_one, p.charW.base.lev.xi_base])

theorem tw_iff (w : D.what₂.places.Pl) : D.plEq w ∈ p.R.twPl ↔ D.what₂.muAt w ≠ D.what₂.mu0 := by
  constructor
  · intro hw he
    apply p.charW.tup.mu_ne (D.plEq w) hw
    rw [← p.tupAt w, he, p.tupleRead_baseTuple_eq_family]
  · intro hne
    by_contra hw
    apply hne
    rw [← p.tupTie _ (Or.inr ⟨w, rfl⟩), ← p.tupTie _ (Or.inl rfl), p.tupAt w, p.charW.tup.mu_off (D.plEq w) hw, p.tupleRead_baseTuple_eq_family]

namespace Realised

variable {p} (h : p.Realised)
include h

end Realised

end PtAt

abbrev Pt {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) : Type 1 := PtAt (Fm.ex x hx i) Fm.Csz

def FamHyp : FamClass := fun Fm =>
  PageFix Fm ∧ PageWin Fm ∧ Formalism.MainNotions.DIV.Align.SmallFirstModulusBelowScale Fm ∧ TameDistinctF Fm ∧ ChosenWall Fm ∧
    (∃ x0 : ℝ, ∀ x ≥ x0, ∀ (i : Fm.Ix x) u,
      ((Fm.D x i).mem u).C.DGam ∣ minkM (2 * (Fm.D x i).R.f * (Fm.D x i).R.N (Fm.D x i).R.m)) ∧ BoxesF Fm ∧ QDRowsF Fm ∧ Fm.CYL ≤ 9 ∧ Formalism.MainNotions.Pk.DGamSmooth Fm ∧ TwGood Fm ∧
    (∃ CH : ℝ, ChosenE Fm 3 CH) ∧ TuSize Fm ∧ DGamSize Fm

def EvPt {eps : ℝ} (Fm : FamP eps) (Q : ∀ (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x), Pt Fm x hx i → Prop) : Prop :=
  ∃ x0 : ℝ, ∀ (x : ℝ) (hx : Fm.x1 < x), x0 ≤ x → ∀ (i : Fm.Ix x) (p : Pt Fm x hx i), p.Rows → Q x hx i p

def Covol : Prop := Closed FamHyp fun Fm CH =>
  ∃ C0 : ℝ, 0 ≤ C0 ∧ EvPt Fm fun _ _ _ p => ∀ C, C0 ≤ C → (p.S false).L3 (p.N C CH)

def Onto : Prop := Closed FamHyp fun Fm CH => DIVinN Fm →
  ∃ C0 : ℝ, 0 ≤ C0 ∧ EvPt Fm fun _ _ _ p => ∀ C, C0 ≤ C → (p.S false).ON (p.N C CH)

end GlobalTheory.BigTop

end
