module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Source.SplitRelativePrism

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem realPlaneSplitNormalize_pair (representation : Rep ℂ RealPlaneGroup)
    (cycle : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl representation)
    (first second : RealPlaneGroup) :
    (splitMixedNormalize realPlaneSplitting representation cycle).val (first, second) =
      representation.ρ (SemidirectProduct.inl first.left)
        (splitEdgeCycle realPlaneSplitting representation first.right cycle
            (realPlaneRadicalAction first.right second.left) +
          representation.ρ (SemidirectProduct.inl (realPlaneRadicalAction first.right second.left))
            (cycle.val (SemidirectProduct.inr first.right, SemidirectProduct.inr second.right))) := by
  have transported : splitRadicalInput realPlaneSplitting first.right
      (realPlaneRadicalAction first.right second.left) = second.left := by
    rw [realPlaneSplitting_input]
    simp [realRadicalInverseLevi]
  have equality := splitMixedNormalize_value realPlaneSplitting representation cycle
    first.left (realPlaneRadicalAction first.right second.left) first.right second.right
  rw [transported] at equality
  change (splitMixedNormalize realPlaneSplitting representation cycle).val
      (SemidirectProduct.inl first.left * SemidirectProduct.inr first.right,
        SemidirectProduct.inl second.left * SemidirectProduct.inr second.right) = _ at equality
  rw [← SemidirectProduct.mk_eq_inl_mul_inr, ← SemidirectProduct.mk_eq_inl_mul_inr] at equality
  exact equality

theorem realPlaneSplitNormalize_homogeneous (representation : Rep ℂ RealPlaneGroup)
    (cycle : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl representation)
    (vertices : Fin 3 → RealPlaneGroup) :
    let first := (vertices 0)⁻¹ * vertices 1
    let second := (vertices 1)⁻¹ * vertices 2
    groupHomogeneousTwoValue representation (splitMixedNormalize realPlaneSplitting representation cycle).val vertices =
      representation.ρ (vertices 0 * SemidirectProduct.inl first.left)
        (splitEdgeCycle realPlaneSplitting representation first.right cycle
            (realPlaneRadicalAction first.right second.left) +
          representation.ρ (SemidirectProduct.inl (realPlaneRadicalAction first.right second.left))
            (cycle.val (SemidirectProduct.inr first.right, SemidirectProduct.inr second.right))) := by
  dsimp only
  rw [groupHomogeneousTwoValue, realPlaneSplitNormalize_pair, map_mul, Module.End.mul_apply]

theorem sourceRelativeProjectedValue_normalize {degree : ℕ} (data : InducingData degree)
    (cycle : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
      (realPlaneLevelCuspidalRep degree data.cusp data.chi))
    (projection : RealGL3 → RealPlaneGroup) (real : RealGL3) (vertices : Fin 3 → RealGL3) :
    let representation := realPlaneLevelCuspidalRep degree data.cusp data.chi
    let points (index : Fin 3) := projection (real * vertices index)
    let first := (points 0)⁻¹ * points 1
    let second := (points 1)⁻¹ * points 2
    sourceRelativeProjectedValue data (splitMixedNormalize realPlaneSplitting representation cycle)
        projection real vertices =
      cuspidalTensorMap data.cusp (realCoefficientComponent degree data.chi real⁻¹)
        (representation.ρ (points 0 * SemidirectProduct.inl first.left)
          (splitEdgeCycle realPlaneSplitting representation first.right cycle
              (realPlaneRadicalAction first.right second.left) +
            representation.ρ (SemidirectProduct.inl (realPlaneRadicalAction first.right second.left))
              (cycle.val (SemidirectProduct.inr first.right, SemidirectProduct.inr second.right)))).val := by
  dsimp only
  rw [sourceRelativeProjectedValue, realPlaneSplitNormalize_homogeneous]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
