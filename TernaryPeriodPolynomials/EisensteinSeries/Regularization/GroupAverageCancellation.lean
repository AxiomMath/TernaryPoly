module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.BoundedGroupAverages

@[expose] public section


open MeasureTheory

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem rightGroupAverage_translation_difference_bound
    {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G]
    (measure : Measure G) [measure.IsMulLeftInvariant]
    {function kernel : G → ℂ} (measurable : Measurable function)
    (kernel_integrable : Integrable kernel measure) {bound : ℝ}
    (bounded : ∀ point, ‖function point‖ ≤ bound) (translation point : G) :
    ‖rightGroupAverage measure function kernel point - rightGroupAverage measure function kernel (translation * point)‖ ≤
      bound * ∫ shift, ‖kernel ((point⁻¹ * translation⁻¹ * point) * shift) - kernel shift‖ ∂measure := by
  let conjugate := point⁻¹ * translation⁻¹ * point
  have translated_integrable := kernel_integrable.comp_mul_left conjugate
  have first_integrable := rightGroupAverage_integrable measure measurable kernel_integrable bounded point
  have second_integrable := rightGroupAverage_integrable measure measurable translated_integrable bounded point
  rw [rightGroupAverage_left_translate_kernel, rightGroupAverage, ← integral_sub first_integrable second_integrable]
  have estimate := norm_integral_le_of_norm_le
    (f := fun shift => function (point * shift) * kernel shift - function (point * shift) * kernel (conjugate * shift))
    ((translated_integrable.sub kernel_integrable).norm.const_mul bound)
    (Filter.Eventually.of_forall (fun shift => by
      rw [← mul_sub, norm_mul, norm_sub_rev (kernel shift)]
      exact mul_le_mul_of_nonneg_right (bounded _) (norm_nonneg _)))
  simpa only [integral_const_mul, Pi.sub_apply, conjugate] using estimate

theorem rightGroupAverage_bound_of_zero_average
    {G A : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableSpace A]
    (measure : Measure G) [SFinite measure] [measure.IsMulLeftInvariant]
    (parameterMeasure : Measure A) [IsProbabilityMeasure parameterMeasure]
    {function kernel : G → ℂ} (measurable : Measurable function) (kernel_measurable : Measurable kernel)
    (kernel_integrable : Integrable kernel measure) {bound : ℝ} (bound_nonnegative : 0 ≤ bound)
    (bounded : ∀ point, ‖function point‖ ≤ bound) (translations : A → G)
    (translations_measurable : Measurable translations)
    (zero : ∀ point, (∫ parameter, function (translations parameter * point) ∂parameterMeasure) = 0)
    (point : G) {decay : ℝ}
    (kernel_bound : ∀ᵐ parameter ∂parameterMeasure,
      (∫ shift, ‖kernel ((point⁻¹ * (translations parameter)⁻¹ * point) * shift) - kernel shift‖ ∂measure) ≤ decay) :
    ‖rightGroupAverage measure function kernel point‖ ≤ bound * decay := by
  have average_zero := rightGroupAverage_preserves_zero_average measure parameterMeasure measurable
    kernel_integrable bounded translations translations_measurable zero point
  have average_measurable := rightGroupAverage_measurable measure measurable kernel_measurable
  have average_integrable : Integrable
      (fun parameter => rightGroupAverage measure function kernel (translations parameter * point)) parameterMeasure :=
    Integrable.of_bound (average_measurable.comp (translations_measurable.mul_const point)).aestronglyMeasurable
      (bound * ∫ shift, ‖kernel shift‖ ∂measure)
      (Filter.Eventually.of_forall (fun _ => rightGroupAverage_bound measure function kernel_integrable bounded _))
  have identity : (∫ parameter,
      rightGroupAverage measure function kernel point -
        rightGroupAverage measure function kernel (translations parameter * point) ∂parameterMeasure) =
      rightGroupAverage measure function kernel point := by
    rw [integral_sub (integrable_const _) average_integrable, average_zero, integral_const]
    simp
  rw [← identity]
  have estimate := norm_integral_le_of_norm_le (μ := parameterMeasure)
    (f := fun parameter => rightGroupAverage measure function kernel point -
      rightGroupAverage measure function kernel (translations parameter * point))
    (integrable_const (bound * decay)) (by
      filter_upwards [kernel_bound] with parameter parameter_bound
      exact (rightGroupAverage_translation_difference_bound measure measurable kernel_integrable bounded
        (translations parameter) point).trans (mul_le_mul_of_nonneg_left parameter_bound bound_nonnegative))
  simpa using estimate

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
