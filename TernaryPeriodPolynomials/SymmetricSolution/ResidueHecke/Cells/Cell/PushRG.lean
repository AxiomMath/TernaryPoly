module

public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.Cell.TreeRes
public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.Cell.Push
public import TernaryPeriodPolynomials.GroupCohomology.Homology.ResolutionConj

@[expose] public section


/-!
# The cell push-forward through the oriented cell complex `RG`

Formalized by Claude Sonnet 5.5.

`RG_projRes PH` restricted to `P_N` is identified with the restriction to `P_N` (along `jPN`) of the cellular
permutation complex through `RG_resIso` (`thetaRG`).  `pushRG n : CxN PN (YAR (RG_projRes PH) (FibRep n)) ⟶ cellCoinv W`
is the induced chain map `[a ⊗ r] ↦ [lof a ⊗ RG_resIso r]` (`pushRG_mk`).  It satisfies `pushRG_comparison`
(`H₃(pushRG) ≫ cellGroupHomologyMap = (eNR)⁻¹ ≫ groupHomology.map jPN (lofN n)`), hence `pushRG_iotaStar`: a top
cycle representing the class of `w` is pushed to a cell cycle whose group-homology class is `ι_* w`; and
`pushRG_QY`: its image under `QY` represents the corestriction.
-/

open CategoryTheory MonoidalCategory Representation Limits
open scoped TensorProduct

noncomputable section

namespace TernaryPeriodPolynomials.Argument.AppendixBResidue

open TernaryPeriodPolynomials.Argument.GroupHomology
open TernaryPeriodPolynomials.Argument.Lemma33.Retract
open TernaryPoly TernaryPoly.IntegralGL3Congruence
open TernaryPeriodPolynomials.Argument.HochschildSerre

/-- The classical decidable equality for `P_N` (matching Mathlib's `classical`-built comparisons). -/
local instance (priority := high) decEqPN' : DecidableEq PN := fun a b => Classical.propDecidable (a = b)

/-- `Res_{PN}` of the oriented cell complex maps to the restricted cell resolution. -/
def thetaRG : (((Rep.resFunctor.{0} PN.subtype).mapHomologicalComplex (ComplexShape.down ℕ)).obj (RGH PH)) ⟶
    cellResPN.complex :=
  ((Rep.resFunctor.{0} jPN).mapHomologicalComplex (ComplexShape.down ℕ)).map RG_resIso.hom

/-- First step: the induced map on the coinvariants of the restricted resolutions. -/
def pushRG1 (n : ℕ) : CxN PN (YAR (RG_projRes PH) (FibRep n)) ⟶ cellCoinvPN (Rep.res PN.subtype (FibRep n)) :=
  (show (((Rep.coinvariantsTensor ℚ PN).obj (Rep.res PN.subtype (FibRep n))).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (((Rep.resFunctor.{0} PN.subtype).mapHomologicalComplex (ComplexShape.down ℕ)).obj (RGH PH)) ⟶
      (((Rep.coinvariantsTensor ℚ PN).obj (Rep.res PN.subtype (FibRep n))).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj cellResPN.complex from
    ((((Rep.coinvariantsTensor ℚ PN).obj (Rep.res PN.subtype (FibRep n))).mapHomologicalComplex
      (ComplexShape.down ℕ)).map thetaRG))

/-- **The cell push-forward through the oriented cell complex**: `[a ⊗ r] ↦ [lof a ⊗ r]`. -/
def pushRG (n : ℕ) : CxN PN (YAR (RG_projRes PH) (FibRep n)) ⟶
    cellCoinv (Rep.res principalSix.subtype (ResRep n)) :=
  pushRG1 n ≫ cellPush (Rep.res PN.subtype (FibRep n)) (Rep.res principalSix.subtype (ResRep n)) (lofN n)

theorem pushRG_mk (n j : ℕ) (a : (FibRep n).V) (r : ((RG_projRes PH).complex.X j).V) :
    ((pushRG n).f j).hom (Coinvariants.mk ((((FibRep n) ⊗ (RG_projRes PH).complex.X j).ρ).comp PN.subtype)
        (a ⊗ₜ[ℚ] r)) =
      Coinvariants.mk (((Rep.res principalSix.subtype (ResRep n)).ρ.tprod (cellRep j).ρ))
        ((lofN n).hom a ⊗ₜ[ℚ] (RG_resIso.hom.f j).hom r) := rfl

theorem res_proj_pi_zero {K : Type} [Group K] (H : Subgroup K) (S : ProjectiveResolution (Rep.trivial ℚ K ℚ)) :
    ((Rep.resFunctor.{0} H.subtype).mapProjectiveResolution S).π.f 0 =
      (Rep.resFunctor.{0} H.subtype).map (S.π.f 0) := by
  simp
  exact (congrArg (fun m => (Rep.resFunctor.{0} H.subtype).map (S.π.f 0) ≫ m)
    ((Rep.resFunctor.{0} H.subtype).map_id (Rep.trivial ℚ K ℚ))).trans (Category.comp_id _)

theorem thetaRG_aug :
    thetaRG.f 0 ≫ cellResPN.π.f 0 =
      ((Rep.resFunctor.{0} PN.subtype).mapProjectiveResolution (RG_projRes PH)).π.f 0 := by
  rw [res_proj_pi_zero]
  have h1 : (RG_projRes PH).π.f 0 = RGH_aug0 PH := by
    change (RGH_aug PH).f 0 = _
    exact ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _
  have h2 : cellResPN.π.f 0 = (Rep.resFunctor.{0} jPN).map cellAug0 := by
    simp [cellResPN, resRes]
    have e : cellResolution.π.f 0 = cellAug0 := by
      change (cellAug).f 0 = _
      exact ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _
    refine Eq.trans ?_ (congrArg (fun m => (Rep.resFunctor.{0} jPN).map m) e)
    exact (congrArg (fun m => (Rep.resFunctor.{0} jPN).map (cellResolution.π.f 0) ≫ m)
      ((Rep.resFunctor.{0} jPN).map_id (Rep.trivial ℚ principalSix ℚ))).trans (Category.comp_id _)
  rw [h1, h2]
  refine Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun z => ?_))
  have := congrArg (fun t => t.hom (z : Graded 0 →₀ ℚ)) RG_resX_aug
  exact this

/-- `pushRG1` with the domain written as the coinvariants of the restricted resolution. -/
def pushRG1' (n : ℕ) :
    (((Rep.coinvariantsTensor ℚ PN).obj (Rep.res PN.subtype (FibRep n))).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (((Rep.resFunctor.{0} PN.subtype).mapHomologicalComplex (ComplexShape.down ℕ)).obj (RGH PH)) ⟶
      cellCoinvPN (Rep.res PN.subtype (FibRep n)) :=
  ((((Rep.coinvariantsTensor ℚ PN).obj (Rep.res PN.subtype (FibRep n))).mapHomologicalComplex
      (ComplexShape.down ℕ)).map thetaRG)

/-- `groupHomologyIso` does not depend on the chosen decidable equality. -/
theorem groupHomologyIso_irrel {G : Type} [Group G] (i1 i2 : DecidableEq G) (A : Rep.{0} ℚ G) (m : ℕ)
    (S : ProjectiveResolution (Rep.trivial ℚ G ℚ)) :
    @groupHomologyIso ℚ G _ _ i1 A m S = @groupHomologyIso ℚ G _ _ i2 A m S := by
  cases Subsingleton.elim i1 i2
  rfl

theorem eNR_eq (n : ℕ) : eNR PN (RG_projRes PH) (FibRep n) 3 =
    groupHomologyIso (Rep.res PN.subtype (FibRep n)) 3
      ((Rep.resFunctor PN.subtype).mapProjectiveResolution (RG_projRes PH)) :=
  groupHomologyIso_irrel _ _ _ _ _

theorem pushRG1'_comparison (n : ℕ) :
    (eNR PN (RG_projRes PH) (FibRep n) 3).hom ≫ HomologicalComplex.homologyMap (pushRG1' n) 3 =
      (groupHomologyIso (Rep.res PN.subtype (FibRep n)) 3 cellResPN).hom := by
  rw [eNR_eq]
  exact groupHomologyIso_hom_comp (k := ℚ) (G := PN) (Rep.res PN.subtype (FibRep n)) 3
    (P := (Rep.resFunctor.{0} PN.subtype).mapProjectiveResolution (RG_projRes PH)) (Q := cellResPN)
    thetaRG thetaRG_aug

theorem pushRG_comparison (n : ℕ) :
    HomologicalComplex.homologyMap (pushRG n) 3 ≫
        cellGroupHomologyMap (Rep.res principalSix.subtype (ResRep n)) 3 =
      (eNR PN (RG_projRes PH) (FibRep n) 3).inv ≫ groupHomology.map jPN (lofN n) 3 := by
  have h1 := pushRG1'_comparison n
  have h2 := cellPush_comparison (Rep.res PN.subtype (FibRep n)) (Rep.res principalSix.subtype (ResRep n))
    (lofN n) 3
  have h3 : HomologicalComplex.homologyMap (pushRG1' n) 3 =
      (eNR PN (RG_projRes PH) (FibRep n) 3).inv ≫
        (groupHomologyIso (Rep.res PN.subtype (FibRep n)) 3 cellResPN).hom :=
    (Iso.eq_inv_comp _).2 h1
  have h4 : HomologicalComplex.homologyMap (pushRG n) 3 =
      HomologicalComplex.homologyMap (pushRG1' n) 3 ≫ HomologicalComplex.homologyMap
        (cellPush (Rep.res PN.subtype (FibRep n)) (Rep.res principalSix.subtype (ResRep n)) (lofN n)) 3 :=
    HomologicalComplex.homologyMap_comp (pushRG1' n) _ 3
  rw [h4, h3]
  erw [Category.assoc, Category.assoc, h2]
  erw [← Category.assoc (groupHomologyIso (Rep.res PN.subtype (FibRep n)) 3 cellResPN).hom, Iso.hom_inv_id,
    Category.id_comp]

theorem pushRG_cycle (n : ℕ) (ζ : (CxN PN (YAR (RG_projRes PH) (FibRep n))).X 3)
    (hζ : ((CxN PN (YAR (RG_projRes PH) (FibRep n))).d 3 2).hom ζ = 0) :
    ((cellCoinv (Rep.res principalSix.subtype (ResRep n))).d 3 2).hom (((pushRG n).f 3).hom ζ) = 0 := by
  have := congrArg (fun t => t.hom ζ) ((pushRG n).comm 3 2)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at this
  rw [this, hζ, map_zero]

/-- **The pushed cycle represents `ι_* w`.** -/
theorem pushRG_iotaStar (n : ℕ) (w : groupHomology (Rep.res PN.subtype (FibRep n)) 3)
    (ζ : (CxN PN (YAR (RG_projRes PH) (FibRep n))).X 3)
    (hζ : ((CxN PN (YAR (RG_projRes PH) (FibRep n))).d 3 2).hom ζ = 0)
    (hcl : cycleClass (CxN PN (YAR (RG_projRes PH) (FibRep n))) ζ hζ =
      (eNR PN (RG_projRes PH) (FibRep n) 3).hom.hom w) :
    (cellGroupHomologyMap (Rep.res principalSix.subtype (ResRep n)) 3).hom
      (cellClass (Rep.res principalSix.subtype (ResRep n)) (((pushRG n).f 3).hom ζ)
        (pushRG_cycle n ζ hζ)) = iotaStar n w := by
  rw [cellClass_eq_cycleClass, ← homologyMap_cycleClass (pushRG n) ζ hζ (pushRG_cycle n ζ hζ), hcl]
  have h := pushRG_comparison n
  have h2 := congrArg (fun t => t.hom ((eNR PN (RG_projRes PH) (FibRep n) 3).hom.hom w)) h
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h2
  refine h2.trans ?_
  have h3 := congrArg (fun t => t.hom w) (Iso.hom_inv_id (eNR PN (RG_projRes PH) (FibRep n) 3))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h3
  rw [h3]
  rfl

/-- **The `P_H`-level image cycle represents the corestriction.** -/
theorem pushRG_QY (n : ℕ) (w : groupHomology (Rep.res PN.subtype (FibRep n)) 3)
    (ζ : (CxN PN (YAR (RG_projRes PH) (FibRep n))).X 3)
    (hζ : ((CxN PN (YAR (RG_projRes PH) (FibRep n))).d 3 2).hom ζ = 0)
    (hcl : cycleClass (CxN PN (YAR (RG_projRes PH) (FibRep n))) ζ hζ =
      (eNR PN (RG_projRes PH) (FibRep n) 3).hom.hom w) :
    ∃ hz' : ((CxK (YAR (RG_projRes PH) (FibRep n))).d 3 2).hom
        (((QY PN (YAR (RG_projRes PH) (FibRep n))).f 3).hom ζ) = 0,
      cycleClass (CxK (YAR (RG_projRes PH) (FibRep n)))
        (((QY PN (YAR (RG_projRes PH) (FibRep n))).f 3).hom ζ) hz' =
          (eKR (RG_projRes PH) (FibRep n) 3).hom.hom (corN PN (FibRep n) 3 w) := by
  have hz' : ((CxK (YAR (RG_projRes PH) (FibRep n))).d 3 2).hom
      (((QY PN (YAR (RG_projRes PH) (FibRep n))).f 3).hom ζ) = 0 := by
    have := congrArg (fun t => t.hom ζ) ((QY PN (YAR (RG_projRes PH) (FibRep n))).comm 3 2)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at this
    rw [this, hζ, map_zero]
  refine ⟨hz', ?_⟩
  rw [← homologyMap_cycleClass (QY PN (YAR (RG_projRes PH) (FibRep n))) ζ hζ hz', hcl, eKR_corN]

end TernaryPeriodPolynomials.Argument.AppendixBResidue
