module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Source.ChosenRelative

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def groupHomogeneousTwoValue {G : Type} [Group G] (representation : Rep ℂ G)
    (cochain : G × G → representation) (vertices : Fin 3 → G) : representation :=
  representation.ρ (vertices 0) (cochain ((vertices 0)⁻¹ * vertices 1, (vertices 1)⁻¹ * vertices 2))

def groupHomogeneousOneValue {G : Type} [Group G] (representation : Rep ℂ G)
    (cochain : G → representation) (vertices : Fin 2 → G) : representation :=
  representation.ρ (vertices 0) (cochain ((vertices 0)⁻¹ * vertices 1))

theorem homogeneousGroupTwoCocycle_recover {G : Type} [Group G] (representation : Rep ℂ G)
    (cochain : (Fin 3 → G) → representation)
    (equivariant : ∀ element vertices, cochain (fun index => element * vertices index) =
      representation.ρ element (cochain vertices))
    (closed : ∀ vertices : Fin 4 → G,
      cochain ![vertices 1, vertices 2, vertices 3] - cochain ![vertices 0, vertices 2, vertices 3] +
        cochain ![vertices 0, vertices 1, vertices 3] - cochain ![vertices 0, vertices 1, vertices 2] = 0)
    (vertices : Fin 3 → G) :
    groupHomogeneousTwoValue representation (homogeneousGroupTwoCocycle representation cochain equivariant closed)
      vertices = cochain vertices := by
  change representation.ρ (vertices 0)
    (cochain ![1, (vertices 0)⁻¹ * vertices 1,
      ((vertices 0)⁻¹ * vertices 1) * ((vertices 1)⁻¹ * vertices 2)]) = _
  rw [← equivariant]
  congr 1
  funext index
  fin_cases index <;> simp [mul_assoc]

theorem groupHomogeneousTwoValue_boundary {G : Type} [Group G] (representation : Rep ℂ G)
    (primitive : G → representation) (vertices : Fin 3 → G) :
    groupHomogeneousTwoValue representation (twoBoundaryCycle representation primitive) vertices =
      groupHomogeneousOneValue representation primitive ![vertices 1, vertices 2] -
        groupHomogeneousOneValue representation primitive ![vertices 0, vertices 2] +
        groupHomogeneousOneValue representation primitive ![vertices 0, vertices 1] := by
  simp only [groupHomogeneousTwoValue, twoBoundaryCycle_apply, groupHomogeneousOneValue,
    Matrix.cons_val_zero, Matrix.cons_val_one, map_sub, map_add]
  rw [← Module.End.mul_apply, ← map_mul]
  simp only [mul_inv_cancel_left, mul_assoc]

theorem sourcePlaneCuspidalValues_recover_level {degree : ℕ} (data : InducingData degree)
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data .plane source)
    (vertices : Fin 3 → RealPlaneGroup) :
    sourcePlaneCuspidalValues data source cocycle (fun index => realPlaneMatrix (vertices index)) 1 =
      (groupHomogeneousTwoValue (realPlaneLevelCuspidalRep degree data.cusp data.chi)
        (sourcePlaneLevelGroupCocycle data source cocycle) vertices).val := by
  exact (homogeneousGroupTwoCocycle_recover (realPlaneCuspidalRep degree data.cusp data.chi)
    (sourcePlaneGroupHomogeneous data source cocycle)
    (sourcePlaneGroupHomogeneous_equivariant data source cocycle)
    (sourcePlaneGroupHomogeneous_closed data source cocycle) vertices).symm

theorem sourcePlaneCuspidalValues_relative_formula {degree : ℕ} (data : InducingData degree)
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data .plane source)
    (primitive : RealPlaneRadical → realPlaneLevelCuspidalRep degree data.cusp data.chi)
    (relative : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
      (realPlaneLevelCuspidalRep degree data.cusp data.chi))
    (formula : relative.val = sourcePlaneLevelGroupCocycle data source cocycle -
      twoBoundaryCycle _ (realPlanePrimitiveExtension _ primitive))
    (vertices : Fin 3 → RealPlaneGroup) :
    sourcePlaneCuspidalValues data source cocycle (fun index => realPlaneMatrix (vertices index)) 1 =
      (groupHomogeneousTwoValue (realPlaneLevelCuspidalRep degree data.cusp data.chi) relative.val vertices).val +
        ((groupHomogeneousOneValue (realPlaneLevelCuspidalRep degree data.cusp data.chi)
              (realPlanePrimitiveExtension _ primitive) ![vertices 1, vertices 2]).val -
          (groupHomogeneousOneValue (realPlaneLevelCuspidalRep degree data.cusp data.chi)
              (realPlanePrimitiveExtension _ primitive) ![vertices 0, vertices 2]).val +
          (groupHomogeneousOneValue (realPlaneLevelCuspidalRep degree data.cusp data.chi)
              (realPlanePrimitiveExtension _ primitive) ![vertices 0, vertices 1]).val) := by
  have reconstruct (first second : RealPlaneGroup) :
      sourcePlaneLevelGroupCocycle data source cocycle (first, second) =
        relative.val (first, second) +
          twoBoundaryCycle _ (realPlanePrimitiveExtension _ primitive) (first, second) := by
    have value := congrArg (fun cycle : groupCohomology.cocycles₂
      (realPlaneLevelCuspidalRep degree data.cusp data.chi) => cycle (first, second)) formula
    change relative.val (first, second) = sourcePlaneLevelGroupCocycle data source cocycle (first, second) -
      twoBoundaryCycle _ (realPlanePrimitiveExtension _ primitive) (first, second) at value
    exact (eq_sub_iff_add_eq.mp value).symm
  rw [sourcePlaneCuspidalValues_recover_level]
  have equality : groupHomogeneousTwoValue (realPlaneLevelCuspidalRep degree data.cusp data.chi)
        (sourcePlaneLevelGroupCocycle data source cocycle) vertices =
      groupHomogeneousTwoValue (realPlaneLevelCuspidalRep degree data.cusp data.chi) relative.val vertices +
        groupHomogeneousTwoValue (realPlaneLevelCuspidalRep degree data.cusp data.chi)
          (twoBoundaryCycle _ (realPlanePrimitiveExtension _ primitive)) vertices := by
    simp only [groupHomogeneousTwoValue, reconstruct, map_add]
  rw [equality, groupHomogeneousTwoValue_boundary]
  rfl

end TernaryPeriodPolynomials.SphericalDetection.Helpers
