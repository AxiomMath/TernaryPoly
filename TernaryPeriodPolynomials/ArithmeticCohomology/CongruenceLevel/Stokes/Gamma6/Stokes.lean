module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Gamma6.Faces

@[expose] public section


/-!
# Lemma `ar:lem:stokes` at level `Γ(6)` for the face groups of `Γ(6) ⊂ SL₃(ℤ)`

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory
open scoped MatrixGroups

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNStokes

open TernaryPeriodPolynomials.Argument.ConvergenceC4
open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
open TernaryPeriodPolynomials.Argument.GammaNFacesFull
open TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPoly.BoundaryFaceResolutionComparison

section Transport

variable {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (gammaN 6) V)

/-- The representation of the model group `Γ(6)` obtained by transport along `Γ(6) ≃ principalSix`. -/
def rep6 (ρ : Representation ℂ (gammaN 6) V) : Representation ℂ Γ6 V :=
  ρ.comp (gammaSixEquiv.symm : Γ6 ≃* gammaN 6).toMonoidHom

theorem toGamma6_hT (g : Γ6) (v : Rep.of ρ) :
    (LinearMap.id : Rep.of ρ →ₗ[ℂ] Rep.of (rep6 ρ))
      ((Rep.of ρ).ρ ((gammaSixEquiv.symm : Γ6 ≃* gammaN 6).toMonoidHom g) v) =
    (Rep.of (rep6 ρ)).ρ g ((LinearMap.id : Rep.of ρ →ₗ[ℂ] Rep.of (rep6 ρ)) v) := rfl

/-- **Transport of `H²(Γ(6) ⊂ SL₃(ℤ), E)` to `H²` of the model group.** -/
def toGamma6 : groupCohomology.H2 (Rep.of ρ) →ₗ[ℂ] groupCohomology.H2 (Rep.of (rep6 ρ)) :=
  EdgeNat.h2Map (gammaSixEquiv.symm : Γ6 ≃* gammaN 6).toMonoidHom (Rep.of ρ) (Rep.of (rep6 ρ)) LinearMap.id
    (toGamma6_hT ρ)

theorem toGamma6_dual_hT (g : Γ6) (v : Rep.of ρ.dual) :
    (LinearMap.id : Rep.of ρ.dual →ₗ[ℂ] Rep.of (rep6 ρ).dual)
      ((Rep.of ρ.dual).ρ ((gammaSixEquiv.symm : Γ6 ≃* gammaN 6).toMonoidHom g) v) =
    (Rep.of (rep6 ρ).dual).ρ g ((LinearMap.id : Rep.of ρ.dual →ₗ[ℂ] Rep.of (rep6 ρ).dual) v) := by
  change ρ.dual (gammaSixEquiv.symm g) v = (rep6 ρ).dual g v
  simp [Representation.dual_apply, rep6, map_inv]

/-- … for the dual coefficient module. -/
def toGamma6Dual : groupCohomology.H2 (Rep.of ρ.dual) →ₗ[ℂ] groupCohomology.H2 (Rep.of (rep6 ρ).dual) :=
  EdgeNat.h2Map (gammaSixEquiv.symm : Γ6 ≃* gammaN 6).toMonoidHom (Rep.of ρ.dual) (Rep.of (rep6 ρ).dual) LinearMap.id
    (toGamma6_dual_hT ρ)

end Transport


section Compare

variable {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (gammaN 6) V)
  {K : Type} [Group K] (ι : K →* gammaN 6)

theorem cmp_hT (s : K) (v : Rep.res ι (Rep.of ρ)) :
    (LinearMap.id : Rep.res ι (Rep.of ρ) →ₗ[ℂ] Rep.res ((gammaSixEquiv : gammaN 6 →* Γ6).comp ι) (Rep.of (rep6 ρ)))
      ((Rep.res ι (Rep.of ρ)).ρ ((MonoidHom.id K) s) v) =
    (Rep.res ((gammaSixEquiv : gammaN 6 →* Γ6).comp ι) (Rep.of (rep6 ρ))).ρ s
      ((LinearMap.id : Rep.res ι (Rep.of ρ) →ₗ[ℂ] Rep.res ((gammaSixEquiv : gammaN 6 →* Γ6).comp ι) (Rep.of (rep6 ρ))) v) := by
  change ρ (ι s) v = ρ (gammaSixEquiv.symm (gammaSixEquiv (ι s))) v
  rw [MulEquiv.symm_apply_apply]

/-- The identity comparison of the restriction of `E` to a subgroup of `Γ(6)` with the restriction of the transported module. -/
def cmpH2 : groupCohomology.H2 (Rep.res ι (Rep.of ρ)) →ₗ[ℂ]
    groupCohomology.H2 (Rep.res ((gammaSixEquiv : gammaN 6 →* Γ6).comp ι) (Rep.of (rep6 ρ))) :=
  EdgeNat.h2Map (MonoidHom.id K) (Rep.res ι (Rep.of ρ))
    (Rep.res ((gammaSixEquiv : gammaN 6 →* Γ6).comp ι) (Rep.of (rep6 ρ))) LinearMap.id (cmp_hT ρ ι)

theorem cmpH2_res (c : groupCohomology.H2 (Rep.of ρ)) :
    cmpH2 ρ ι (twoCohomologyRestriction ι (Rep.of ρ) c) =
      twoCohomologyRestriction ((gammaSixEquiv : gammaN 6 →* Γ6).comp ι) (Rep.of (rep6 ρ)) (toGamma6 ρ c) := by
  obtain ⟨z, rfl⟩ := twoCocycle_H2_surjective (Rep.of ρ) c
  unfold cmpH2 toGamma6
  rw [twoCohomologyRestriction_apply, EdgeNat.h2Map_π, EdgeNat.h2Map_π, twoCohomologyRestriction_apply]
  congr 1
  apply Subtype.ext
  funext x
  obtain ⟨a, b⟩ := x
  change z.1 (ι a, ι b) = z.1 (gammaSixEquiv.symm (gammaSixEquiv (ι a)), gammaSixEquiv.symm (gammaSixEquiv (ι b)))
  rw [MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]

theorem cmpDual_hT (s : K) (v : Rep.res ι (Rep.of ρ.dual)) :
    (LinearMap.id : Rep.res ι (Rep.of ρ.dual) →ₗ[ℂ] Rep.res ((gammaSixEquiv : gammaN 6 →* Γ6).comp ι) (Rep.of (rep6 ρ).dual))
      ((Rep.res ι (Rep.of ρ.dual)).ρ ((MonoidHom.id K) s) v) =
    (Rep.res ((gammaSixEquiv : gammaN 6 →* Γ6).comp ι) (Rep.of (rep6 ρ).dual)).ρ s
      ((LinearMap.id : Rep.res ι (Rep.of ρ.dual) →ₗ[ℂ] Rep.res ((gammaSixEquiv : gammaN 6 →* Γ6).comp ι) (Rep.of (rep6 ρ).dual)) v) := by
  change ρ.dual (ι s) v = (rep6 ρ).dual (gammaSixEquiv (ι s)) v
  simp [Representation.dual_apply, rep6, map_inv]

def cmpH2Dual : groupCohomology.H2 (Rep.res ι (Rep.of ρ.dual)) →ₗ[ℂ]
    groupCohomology.H2 (Rep.res ((gammaSixEquiv : gammaN 6 →* Γ6).comp ι) (Rep.of (rep6 ρ).dual)) :=
  EdgeNat.h2Map (MonoidHom.id K) (Rep.res ι (Rep.of ρ.dual))
    (Rep.res ((gammaSixEquiv : gammaN 6 →* Γ6).comp ι) (Rep.of (rep6 ρ).dual)) LinearMap.id (cmpDual_hT ρ ι)

theorem cmpH2Dual_res (c : groupCohomology.H2 (Rep.of ρ.dual)) :
    cmpH2Dual ρ ι (twoCohomologyRestriction ι (Rep.of ρ.dual) c) =
      twoCohomologyRestriction ((gammaSixEquiv : gammaN 6 →* Γ6).comp ι) (Rep.of (rep6 ρ).dual) (toGamma6Dual ρ c) := by
  obtain ⟨z, rfl⟩ := twoCocycle_H2_surjective (Rep.of ρ.dual) c
  unfold cmpH2Dual toGamma6Dual
  rw [twoCohomologyRestriction_apply, EdgeNat.h2Map_π, EdgeNat.h2Map_π, twoCohomologyRestriction_apply]
  congr 1
  apply Subtype.ext
  funext x
  obtain ⟨a, b⟩ := x
  change z.1 (ι a, ι b) = z.1 (gammaSixEquiv.symm (gammaSixEquiv (ι a)), gammaSixEquiv.symm (gammaSixEquiv (ι b)))
  rw [MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]

end Compare


section Mathlib

open TernaryPeriodPolynomials.Argument.TopHomology
open TernaryPoly.EquivariantSingularSmall
open TernaryPoly.SymmetricSpaceBoundaryMV (Flag)
open GeneralEisenstein

attribute [local instance] TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison.vertexAction

variable {V : Type} [AddCommGroup V] [Module ℂ V] [Module ℚ V] [IsScalarTower ℚ ℂ V]
  (ρ : Representation ℂ (gammaN 6) V)

/-- **The face pairing of the line face `i` of `Γ(6)`, on the cohomology of the line group `gammaNQAt 6 i.rep` with coefficients `E` and `E^*`.** -/
def lineFacePairM (i : LineFaces 6)
    (x : groupCohomology.H2 (Rep.res (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) (Rep.of ρ)))
    (y : groupCohomology.H2 (Rep.res (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) (Rep.of ρ.dual))) : ℂ :=
  lineFacePair (rep6 ρ) i
    (cmpH2 ρ (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) x)
    (cmpH2Dual ρ (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) y)

/-- … of the plane face `i`, on the cohomology of the plane group `gammaNPAt 6 h`. -/
def planeFacePairM (i : PlaneFaces 6)
    (x : groupCohomology.H2 (Rep.res (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) (Rep.of ρ)))
    (y : groupCohomology.H2 (Rep.res (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) (Rep.of ρ.dual))) : ℂ :=
  planeFacePair (rep6 ρ) i
    (cmpH2 ρ (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) x)
    (cmpH2Dual ρ (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) y)

/-- **Lemma `ar:lem:stokes` at level `Γ(6) ⊂ SL₃(ℤ)`, for the face groups of the paper.**  For global classes `c`, `c'` of `H²(Γ(6), E)`, `H²(Γ(6), E^*)` (`E^*` the contragredient)
whose geometric representatives have vanishing restrictions to the complete flags: the sum over the line faces `Γ(6) ∩ h⁻¹Qh` of the face pairings of the restrictions of `c`, `c'`
plus the sum over the plane faces `Γ(6) ∩ h⁻¹Ph` vanishes. -/
theorem gamma6_stokes_mathlib
    (c : groupCohomology.H2 (Rep.of ρ)) (c' : groupCohomology.H2 (Rep.of ρ.dual))
    (hflag : ∃ (X : (homCochains (prodComplex Γ6 RationalGL3 PUnit) (qRep (MonoidHom.id Γ6) (rep6 ρ))).homology 2)
        (X' : (homCochains (prodComplex Γ6 RationalGL3 PUnit) (qRep (MonoidHom.id Γ6) (rep6 ρ).dual)).homology 2),
      (fixCoordH (1 : RationalGL3) PUnit.unit (fun _ => rfl) (qRep (MonoidHom.id Γ6) (rep6 ρ)) 2).hom X =
        qH2 (rep6 ρ) (toGamma6 ρ c) ∧
      (fixCoordH (1 : RationalGL3) PUnit.unit (fun _ => rfl) (qRep (MonoidHom.id Γ6) (rep6 ρ).dual) 2).hom X' =
        qH2 (rep6 ρ).dual (toGamma6Dual ρ c') ∧
      (HomologicalComplex.homologyMap (homPullback (ptMap Flag) (qRep (MonoidHom.id Γ6) (rep6 ρ))) 2).hom X = 0 ∧
      (HomologicalComplex.homologyMap (homPullback (ptMap Flag) (qRep (MonoidHom.id Γ6) (rep6 ρ).dual)) 2).hom X' = 0) :
    ∑ i : LineFaces 6, lineFacePairM ρ i
        (twoCohomologyRestriction (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) (Rep.of ρ) c)
        (twoCohomologyRestriction (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) (Rep.of ρ.dual) c') +
      ∑ i : PlaneFaces 6, planeFacePairM ρ i
        (twoCohomologyRestriction (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) (Rep.of ρ) c)
        (twoCohomologyRestriction (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) (Rep.of ρ.dual) c') = 0 := by
  have key := gamma6_stokes_classes (rep6 ρ) (toGamma6 ρ c) (toGamma6Dual ρ c') hflag
  rw [← key]
  congr 1
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    unfold lineFacePairM
    rw [cmpH2_res, cmpH2Dual_res]
    rfl
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    unfold planeFacePairM
    rw [cmpH2_res, cmpH2Dual_res]
    rfl

end Mathlib

end TernaryPeriodPolynomials.Argument.GammaNStokes
