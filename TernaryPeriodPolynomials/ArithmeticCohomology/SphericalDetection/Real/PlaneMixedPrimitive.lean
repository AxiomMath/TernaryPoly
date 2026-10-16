module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Real.PlanePrimitiveExtension
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Real.PlaneMixedCocycles

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem realPlanePrimitiveExtension_levi (representation : Rep ℂ RealPlaneGroup)
    (primitive : RealPlaneRadical → representation) (matrix : BinaryRealGL) :
    realPlanePrimitiveExtension representation primitive (SemidirectProduct.inr matrix) = primitive 1 := rfl

theorem realPlanePrimitiveExtension_radical_levi (representation : Rep ℂ RealPlaneGroup)
    (primitive : RealPlaneRadical → representation) (matrix : BinaryRealGL) (radical : RealPlaneRadical) :
    realPlanePrimitiveExtension representation primitive
      (SemidirectProduct.inl radical * SemidirectProduct.inr matrix) = primitive radical := by
  simp [realPlanePrimitiveExtension]

theorem realPlanePrimitiveExtension_mixed (representation : Rep ℂ RealPlaneGroup)
    (primitive : RealPlaneRadical → representation) (matrix : BinaryRealGL) (radical : RealPlaneRadical) :
    realPlanePrimitiveExtension representation primitive
      (SemidirectProduct.inr matrix * SemidirectProduct.inl (realRadicalInverseLevi matrix radical)) = primitive radical := by
  rw [← realRadicalInverseLevi_product]
  exact realPlanePrimitiveExtension_radical_levi representation primitive matrix radical

theorem realPlanePrimitiveExtension_boundary_mixed (representation : Rep ℂ RealPlaneGroup)
    (primitive : RealPlaneRadical → representation) (unit_zero : primitive 1 = 0)
    (matrix : BinaryRealGL) (radical : RealPlaneRadical) :
    twoBoundaryCycle representation (realPlanePrimitiveExtension representation primitive)
        (SemidirectProduct.inr matrix, SemidirectProduct.inl (realRadicalInverseLevi matrix radical)) -
      twoBoundaryCycle representation (realPlanePrimitiveExtension representation primitive)
        (SemidirectProduct.inl radical, SemidirectProduct.inr matrix) =
      representation.ρ (SemidirectProduct.inr matrix) (primitive (realRadicalInverseLevi matrix radical)) - primitive radical := by
  rw [twoBoundaryCycle_apply, twoBoundaryCycle_apply, realPlanePrimitiveExtension_mixed,
    realPlanePrimitiveExtension_radical, realPlanePrimitiveExtension_radical,
    realPlanePrimitiveExtension_levi, unit_zero, map_zero, realPlanePrimitiveExtension_radical_levi]
  abel

theorem realPlaneRelative_mixed_formula (representation : Rep ℂ RealPlaneGroup)
    (cycle : groupCohomology.cocycles₂ representation) (primitive : RealPlaneRadical → representation)
    (unit_zero : primitive 1 = 0)
    (relative : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl representation)
    (formula : relative.val = cycle - twoBoundaryCycle representation (realPlanePrimitiveExtension representation primitive))
    (matrix : BinaryRealGL) (radical : RealPlaneRadical) :
    relative.val (SemidirectProduct.inr matrix, SemidirectProduct.inl (realRadicalInverseLevi matrix radical)) -
        relative.val (SemidirectProduct.inl radical, SemidirectProduct.inr matrix) =
      cycle (SemidirectProduct.inr matrix, SemidirectProduct.inl (realRadicalInverseLevi matrix radical)) -
        cycle (SemidirectProduct.inl radical, SemidirectProduct.inr matrix) -
          representation.ρ (SemidirectProduct.inr matrix) (primitive (realRadicalInverseLevi matrix radical)) + primitive radical := by
  rw [formula]
  have boundary := realPlanePrimitiveExtension_boundary_mixed representation primitive unit_zero matrix radical
  change (cycle _ - twoBoundaryCycle representation (realPlanePrimitiveExtension representation primitive) _) -
    (cycle _ - twoBoundaryCycle representation (realPlanePrimitiveExtension representation primitive) _) = _
  linear_combination (norm := abel) -boundary

theorem realPlaneRelative_primitive_unit (representation : Rep ℂ RealPlaneGroup)
    (cycle : groupCohomology.cocycles₂ representation) (unit_zero : cycle (1, 1) = 0)
    (primitive : RealPlaneRadical → representation)
    (relative : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl representation)
    (formula : relative.val = cycle - twoBoundaryCycle representation (realPlanePrimitiveExtension representation primitive)) :
    primitive 1 = 0 := by
  have relative_unit := relative.property 1 1
  change relative.val (1, 1) = 0 at relative_unit
  rw [formula] at relative_unit
  change cycle (1, 1) - twoBoundaryCycle representation (realPlanePrimitiveExtension representation primitive) (1, 1) = 0 at relative_unit
  rw [unit_zero, twoBoundaryCycle_apply, map_one, Module.End.one_apply, one_mul] at relative_unit
  change 0 - (primitive 1 - primitive 1 + primitive 1) = 0 at relative_unit
  simpa only [sub_self, zero_add, zero_sub, neg_eq_zero] using relative_unit

end TernaryPeriodPolynomials.SphericalDetection.Helpers
