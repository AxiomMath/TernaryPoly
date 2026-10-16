module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Adelic.Periodicity
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.SeriesIntegrability

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

instance additiveDomain_probability : IsProbabilityMeasure (adeleMeasure.restrict additiveDomain) :=
  ⟨by rw [Measure.restrict_apply_univ, adeleMeasure_additiveDomain]⟩

theorem rational_periodic_shear_integrable {E : Type*} [NormedAddCommGroup E]
    (function : Adeles → E)
    (periodic : ∀ rational : ℚ, ∀ value, function (rationalAdele rational + value) = function value)
    (integrable : IntegrableOn function additiveDomain adeleMeasure)
    (firstMeasure : Measure Adeles) [IsFiniteMeasure firstMeasure]
    (shift : Adeles → Adeles) (shift_measurable : Measurable shift) :
    Integrable (fun coordinates : Adeles × Adeles => function (coordinates.2 - shift coordinates.1))
      (firstMeasure.prod (adeleMeasure.restrict additiveDomain)) := by
  have measurable := (rational_periodic_aestronglyMeasurable function periodic integrable).comp_snd
    (μ := firstMeasure)
  have sheared := measurable.comp_measurePreserving
    (adele_fiber_sub_measurePreserving firstMeasure shift shift_measurable)
  have restricted := sheared.mono_measure
    (Measure.prod_mono le_rfl (Measure.restrict_le_self (s := additiveDomain)))
  apply (integrable_prod_iff restricted).mpr
  constructor
  · filter_upwards with first
    simpa only [IntegrableOn, Function.comp_def, sub_eq_add_neg, add_comm] using
      rational_periodic_integrableOn_add_left function periodic integrable (-shift first)
  · have fiber_norm (first : Adeles) :
        (∫ second in additiveDomain, ‖function (second - shift first)‖ ∂adeleMeasure) =
          ∫ second in additiveDomain, ‖function second‖ ∂adeleMeasure :=
      rational_periodic_integral_sub_right (fun value => ‖function value‖)
        (fun rational value => congrArg norm (periodic rational value)) (shift first)
    simp only [Function.comp_def] at ⊢
    simp_rw [fiber_norm]
    exact integrable_const _

theorem rational_periodic_shear_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E]
    (function : Adeles → E)
    (periodic : ∀ rational : ℚ, ∀ value, function (rationalAdele rational + value) = function value)
    (integrable : IntegrableOn function additiveDomain adeleMeasure)
    (firstMeasure : Measure Adeles) [IsProbabilityMeasure firstMeasure]
    (shift : Adeles → Adeles) (shift_measurable : Measurable shift) :
    (∫ coordinates : Adeles × Adeles, function (coordinates.2 - shift coordinates.1)
      ∂(firstMeasure.prod (adeleMeasure.restrict additiveDomain))) =
        ∫ value in additiveDomain, function value ∂adeleMeasure := by
  rw [integral_prod _
    (rational_periodic_shear_integrable function periodic integrable firstMeasure shift shift_measurable)]
  simp_rw [rational_periodic_integral_sub_right function periodic]
  simp

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
