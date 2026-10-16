module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Adelic.Unfolding

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem integrable_tsum_of_enorm_sum {Domain Index : Type*} [MeasurableSpace Domain]
    [Countable Index] {measure : Measure Domain} {family : Index → Domain → ℂ}
    (measurable : ∀ index, AEStronglyMeasurable (family index) measure)
    (finite_norm_sum : (∑' index, ∫⁻ value, ‖family index value‖ₑ ∂measure) ≠ ⊤) :
    Integrable (fun value => ∑' index, family index value) measure := by
  refine ⟨AEStronglyMeasurable.tsum measurable, ?_⟩
  calc
    (∫⁻ value, ‖∑' index, family index value‖ₑ ∂measure) ≤
        ∫⁻ value, ∑' index, ‖family index value‖ₑ ∂measure :=
      lintegral_mono (fun value => enorm_tsum_le_tsum_enorm (f := fun index => family index value))
    _ = ∑' index, ∫⁻ value, ‖family index value‖ₑ ∂measure :=
      lintegral_tsum (fun index => (measurable index).enorm)
    _ < ⊤ := finite_norm_sum.lt_top

theorem adele_fiber_sub_measurePreserving (firstMeasure : Measure Adeles)
    [SFinite firstMeasure] (shift : Adeles → Adeles) (shift_measurable : Measurable shift) :
    MeasurePreserving (fun coordinates : Adeles × Adeles =>
      (coordinates.1, coordinates.2 - shift coordinates.1))
      (firstMeasure.prod adeleMeasure) (firstMeasure.prod adeleMeasure) := by
  apply (MeasurePreserving.id firstMeasure).skew_product
    (g := fun first second : Adeles => second - shift first)
    (μc := adeleMeasure) (μd := adeleMeasure)
  · exact measurable_snd.sub (shift_measurable.comp measurable_fst)
  · filter_upwards with first
    exact (measurePreserving_sub_right adeleMeasure (shift first)).map_eq

theorem rational_translates_lintegral_sum (function : Adeles → ENNReal) (shift : Adeles) :
    (∑' rational : ℚ, ∫⁻ value in additiveDomain,
      function (value - rationalAdele rational - shift) ∂adeleMeasure) =
      ∫⁻ value, function value ∂adeleMeasure := by
  calc
    _ = ∑' rational : ℚ, ∫⁻ value in additiveDomain,
        function (rationalAdele rational + value - shift) ∂adeleMeasure := by
      simpa only [Equiv.neg_apply, map_neg, sub_neg_eq_add, add_comm] using
        ((Equiv.neg ℚ).tsum_eq (fun rational => ∫⁻ value in additiveDomain,
          function (value - rationalAdele rational - shift) ∂adeleMeasure)).symm
    _ = ∫⁻ value, function (value - shift) ∂adeleMeasure :=
      (adele_lintegral_eq_rational_tsum (fun value => function (value - shift))).symm
    _ = _ := lintegral_sub_right_eq_self function shift

theorem rational_fiber_term_integrable (firstMeasure : Measure Adeles) [SFinite firstMeasure]
    (kernel : Adeles × Adeles → ℂ) (shift : Adeles → Adeles)
    (shift_measurable : Measurable shift)
    (integrable : Integrable kernel (firstMeasure.prod adeleMeasure)) (rational : ℚ) :
    Integrable (fun coordinates : Adeles × Adeles =>
      kernel (coordinates.1, coordinates.2 - rationalAdele rational - shift coordinates.1))
      (firstMeasure.prod (adeleMeasure.restrict additiveDomain)) := by
  have preserving := adele_fiber_sub_measurePreserving firstMeasure
    (fun first => rationalAdele rational + shift first) (measurable_const.add shift_measurable)
  have full_integrable := preserving.integrable_comp_of_integrable integrable
  have restricted_integrable := full_integrable.mono_measure
    (Measure.prod_mono le_rfl (Measure.restrict_le_self (s := additiveDomain)))
  simpa only [Function.comp_def, sub_add_eq_sub_sub] using restricted_integrable

theorem rational_fiber_term_aestronglyMeasurable (firstMeasure : Measure Adeles) [SFinite firstMeasure]
    (kernel : Adeles × Adeles → ℂ) (shift : Adeles → Adeles)
    (shift_measurable : Measurable shift)
    (kernel_measurable : AEStronglyMeasurable kernel (firstMeasure.prod adeleMeasure)) (rational : ℚ) :
    AEStronglyMeasurable (fun coordinates : Adeles × Adeles =>
      kernel (coordinates.1, coordinates.2 - rationalAdele rational - shift coordinates.1))
      (firstMeasure.prod (adeleMeasure.restrict additiveDomain)) := by
  have preserving := adele_fiber_sub_measurePreserving firstMeasure
    (fun first => rationalAdele rational + shift first) (measurable_const.add shift_measurable)
  have full_measurable := kernel_measurable.comp_measurePreserving preserving
  have restricted := full_measurable.mono_measure
    (Measure.prod_mono le_rfl (Measure.restrict_le_self (s := additiveDomain)))
  simpa only [Function.comp_def, sub_add_eq_sub_sub] using restricted

theorem rational_fiber_norm_sum_of_measurable (firstMeasure : Measure Adeles) [SFinite firstMeasure]
    (kernel : Adeles × Adeles → ℂ) (shift : Adeles → Adeles)
    (shift_measurable : Measurable shift)
    (kernel_measurable : AEStronglyMeasurable kernel (firstMeasure.prod adeleMeasure)) :
    (∑' rational : ℚ, ∫⁻ coordinates : Adeles × Adeles,
      ‖kernel (coordinates.1, coordinates.2 - rationalAdele rational - shift coordinates.1)‖ₑ
        ∂(firstMeasure.prod (adeleMeasure.restrict additiveDomain))) =
      ∫⁻ coordinates, ‖kernel coordinates‖ₑ ∂(firstMeasure.prod adeleMeasure) := by
  have measurable (rational : ℚ) :=
    (rational_fiber_term_aestronglyMeasurable firstMeasure kernel shift shift_measurable kernel_measurable rational).enorm
  calc
    _ = ∑' rational : ℚ, ∫⁻ first, ∫⁻ second in additiveDomain,
        ‖kernel (first, second - rationalAdele rational - shift first)‖ₑ
          ∂adeleMeasure ∂firstMeasure := by
      apply tsum_congr
      intro rational
      exact lintegral_prod _ (measurable rational)
    _ = ∫⁻ first, ∑' rational : ℚ, ∫⁻ second in additiveDomain,
        ‖kernel (first, second - rationalAdele rational - shift first)‖ₑ
          ∂adeleMeasure ∂firstMeasure := by
      rw [lintegral_tsum (fun rational => (measurable rational).lintegral_prod_right)]
    _ = ∫⁻ first, ∫⁻ second, ‖kernel (first, second)‖ₑ ∂adeleMeasure ∂firstMeasure := by
      apply lintegral_congr
      intro first
      exact rational_translates_lintegral_sum (fun second => ‖kernel (first, second)‖ₑ) (shift first)
    _ = _ := (lintegral_prod _ kernel_measurable.enorm).symm

theorem rational_fiber_norm_sum (firstMeasure : Measure Adeles) [SFinite firstMeasure]
    (kernel : Adeles × Adeles → ℂ) (shift : Adeles → Adeles)
    (shift_measurable : Measurable shift)
    (integrable : Integrable kernel (firstMeasure.prod adeleMeasure)) :
    (∑' rational : ℚ, ∫⁻ coordinates : Adeles × Adeles,
      ‖kernel (coordinates.1, coordinates.2 - rationalAdele rational - shift coordinates.1)‖ₑ
        ∂(firstMeasure.prod (adeleMeasure.restrict additiveDomain))) =
      ∫⁻ coordinates, ‖kernel coordinates‖ₑ ∂(firstMeasure.prod adeleMeasure) :=
  rational_fiber_norm_sum_of_measurable firstMeasure kernel shift shift_measurable
    integrable.aestronglyMeasurable

theorem rational_fiber_periodization_integrable (firstMeasure : Measure Adeles) [SFinite firstMeasure]
    (kernel : Adeles × Adeles → ℂ) (shift : Adeles → Adeles)
    (shift_measurable : Measurable shift)
    (integrable : Integrable kernel (firstMeasure.prod adeleMeasure)) :
    Integrable (fun coordinates : Adeles × Adeles => ∑' rational : ℚ,
      kernel (coordinates.1, coordinates.2 - rationalAdele rational - shift coordinates.1))
      (firstMeasure.prod (adeleMeasure.restrict additiveDomain)) := by
  apply integrable_tsum_of_enorm_sum
  · intro rational
    exact (rational_fiber_term_integrable firstMeasure kernel shift shift_measurable integrable rational).aestronglyMeasurable
  · rw [rational_fiber_norm_sum firstMeasure kernel shift shift_measurable integrable]
    exact integrable.hasFiniteIntegral.ne

theorem rational_fiber_periodization_norm_le (firstMeasure : Measure Adeles) [SFinite firstMeasure]
    (kernel : Adeles × Adeles → ℂ) (shift : Adeles → Adeles)
    (shift_measurable : Measurable shift)
    (integrable : Integrable kernel (firstMeasure.prod adeleMeasure)) :
    (∫⁻ coordinates : Adeles × Adeles, ‖∑' rational : ℚ,
      kernel (coordinates.1, coordinates.2 - rationalAdele rational - shift coordinates.1)‖ₑ
      ∂(firstMeasure.prod (adeleMeasure.restrict additiveDomain))) ≤
      ∫⁻ coordinates, ‖kernel coordinates‖ₑ ∂(firstMeasure.prod adeleMeasure) := by
  calc
    _ ≤ ∫⁻ coordinates : Adeles × Adeles, ∑' rational : ℚ,
        ‖kernel (coordinates.1, coordinates.2 - rationalAdele rational - shift coordinates.1)‖ₑ
        ∂(firstMeasure.prod (adeleMeasure.restrict additiveDomain)) :=
      lintegral_mono (fun _ => enorm_tsum_le_tsum_enorm)
    _ = ∑' rational : ℚ, ∫⁻ coordinates : Adeles × Adeles,
        ‖kernel (coordinates.1, coordinates.2 - rationalAdele rational - shift coordinates.1)‖ₑ
        ∂(firstMeasure.prod (adeleMeasure.restrict additiveDomain)) :=
      lintegral_tsum (fun rational =>
        (rational_fiber_term_integrable firstMeasure kernel shift shift_measurable integrable rational).aestronglyMeasurable.enorm)
    _ = _ := rational_fiber_norm_sum firstMeasure kernel shift shift_measurable integrable

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
