module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.PositiveEulerBound

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory
open scoped ENNReal

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem goodLinePositiveWeight_integrable (exponent : ℂ) (convergent : 3 < exponent.re) :
    Integrable (goodLinePositiveWeight exponent) (finiteAwayThreeMeasure.prod finiteAwayThreeMeasure) := by
  classical
  have truncated := fun places => goodLinePositiveWeight_truncated_integrable exponent (by linarith) places
  have measurable := AEStronglyMeasurable.iUnion (fun places => (truncated places).aestronglyMeasurable)
  rw [goodLineFiniteSupportRegion_union, Measure.restrict_univ] at measurable
  refine ⟨measurable, ?_⟩
  apply (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall (goodLinePositiveWeight_nonneg exponent))).mpr
  have directed : Directed (· ⊆ ·) goodLineFiniteSupportRegion := by
    intro first second
    exact ⟨first ∪ second, goodLineFiniteSupportRegion_mono Finset.subset_union_left,
      goodLineFiniteSupportRegion_mono Finset.subset_union_right⟩
  have exhaustion := setLIntegral_iUnion_of_directed (μ := finiteAwayThreeMeasure.prod finiteAwayThreeMeasure)
    (fun pair => ENNReal.ofReal (goodLinePositiveWeight exponent pair)) directed
  rw [goodLineFiniteSupportRegion_union, Measure.restrict_univ] at exhaustion
  rw [exhaustion]
  apply lt_of_le_of_lt (iSup_le (fun places => ?_)) (ENNReal.ofReal_lt_top
    (r := Real.exp (2 * ∑' place, positiveEulerMajorant exponent place)))
  rw [← ofReal_integral_eq_lintegral_ofReal (truncated places)
    (Filter.Eventually.of_forall (goodLinePositiveWeight_nonneg exponent))]
  exact ENNReal.ofReal_le_ofReal (goodLinePositiveWeight_uniform_bound exponent convergent places)

end TernaryPeriodPolynomials.SphericalDetection.Helpers
