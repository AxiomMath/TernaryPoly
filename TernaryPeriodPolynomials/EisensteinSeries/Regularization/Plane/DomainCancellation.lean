module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Plane.PeriodDomain

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

local notation "RealSL3" => SpecialLinearGroup (Fin 3) ℝ

theorem principalPlaneDomain_periodic_integral_translate
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (function : RealSL3 → E)
    (periodic : ∀ element : realPlanePeriodSubgroup, ∀ matrix, function (element.val * matrix) = function matrix)
    (first second : ℝ) :
    (∫ matrix in principalPlaneDomain, function (realSpecialPlane first second * matrix) ∂realSpecialLinearHaar) =
      ∫ matrix in principalPlaneDomain, function matrix ∂realSpecialLinearHaar := by
  have identity : (∫ matrix in principalPlaneDomain, function (realSpecialPlane first second * matrix)
      ∂principalPlaneTubeMeasure) = ∫ matrix in principalPlaneDomain, function matrix ∂principalPlaneTubeMeasure := by
    calc
      _ = ∫ matrix in (fun matrix => realSpecialPlane first second * matrix) '' principalPlaneDomain,
          function matrix ∂principalPlaneTubeMeasure :=
        ((principalPlaneTube_translation first second).setIntegral_image_emb
          (MeasurableEquiv.mulLeft (realSpecialPlane first second)).measurableEmbedding function principalPlaneDomain).symm
      _ = _ := (principalPlaneDomain_translate_period_isFundamental first second).setIntegral_eq
        principalPlaneDomain_period_isFundamental periodic
  simpa only [principalPlaneTubeMeasure_restrict_domain] using identity

theorem principalPlaneDomain_periodic_integrable_translate
    {E : Type*} [NormedAddCommGroup E]
    (function : RealSL3 → E)
    (periodic : ∀ element : realPlanePeriodSubgroup, ∀ matrix, function (element.val * matrix) = function matrix)
    (integrable : IntegrableOn function principalPlaneDomain realSpecialLinearHaar) (first second : ℝ) :
    IntegrableOn (fun matrix => function (realSpecialPlane first second * matrix))
      principalPlaneDomain realSpecialLinearHaar := by
  have tube_integrable : IntegrableOn function principalPlaneDomain principalPlaneTubeMeasure := by
    simpa only [IntegrableOn, principalPlaneTubeMeasure_restrict_domain] using integrable
  have translated := (principalPlaneDomain_period_isFundamental.integrableOn_iff
    (principalPlaneDomain_translate_period_isFundamental first second) periodic).mp tube_integrable
  have pulled := ((principalPlaneTube_translation first second).integrableOn_image
    (MeasurableEquiv.mulLeft (realSpecialPlane first second)).measurableEmbedding).mp translated
  simpa only [IntegrableOn, principalPlaneTubeMeasure_restrict_domain, Function.comp_def] using pulled

theorem principalPlaneDomain_integral_zero_of_plane_average
    {function : RealSL3 → ℂ} (measurable : Measurable function)
    (periodic : ∀ element : realPlanePeriodSubgroup, ∀ matrix, function (element.val * matrix) = function matrix)
    (integrable : IntegrableOn function principalPlaneDomain realSpecialLinearHaar)
    (average_zero : ∀ matrix, (∫ point : ℝ × ℝ,
      function (realSpecialPlane (3 * point.1) (3 * point.2) * matrix) ∂realPlaneUnitMeasure) = 0) :
    (∫ matrix in principalPlaneDomain, function matrix ∂realSpecialLinearHaar) = 0 := by
  have translate_continuous : Continuous (fun pair : (ℝ × ℝ) × RealSL3 =>
      realSpecialPlane (3 * pair.1.1) (3 * pair.1.2) * pair.2) :=
    (realSpecialPlane_continuous.comp
      ((continuous_const.mul (continuous_fst.comp continuous_fst)).prodMk
        (continuous_const.mul (continuous_snd.comp continuous_fst)))).mul continuous_snd
  have joint_measurable := measurable.comp translate_continuous.measurable
  dsimp only [Function.comp_def] at joint_measurable
  have norm_integral (point : ℝ × ℝ) :
      (∫ matrix in principalPlaneDomain,
        ‖function (realSpecialPlane (3 * point.1) (3 * point.2) * matrix)‖ ∂realSpecialLinearHaar) =
        ∫ matrix in principalPlaneDomain, ‖function matrix‖ ∂realSpecialLinearHaar :=
    principalPlaneDomain_periodic_integral_translate (fun matrix => ‖function matrix‖)
      (fun element matrix => congrArg norm (periodic element matrix)) _ _
  have joint_integrable : Integrable (fun pair : (ℝ × ℝ) × RealSL3 =>
      function (realSpecialPlane (3 * pair.1.1) (3 * pair.1.2) * pair.2))
      (realPlaneUnitMeasure.prod (realSpecialLinearHaar.restrict principalPlaneDomain)) := by
    apply (integrable_prod_iff joint_measurable.aestronglyMeasurable).mpr
    refine ⟨Filter.Eventually.of_forall (fun point : ℝ × ℝ =>
      principalPlaneDomain_periodic_integrable_translate function periodic integrable (3 * point.1) (3 * point.2)), ?_⟩
    simpa only [norm_integral] using
      (integrable_const (μ := realPlaneUnitMeasure)
        (∫ matrix in principalPlaneDomain, ‖function matrix‖ ∂realSpecialLinearHaar))
  calc
    _ = ∫ point : ℝ × ℝ, ∫ matrix in principalPlaneDomain,
        function (realSpecialPlane (3 * point.1) (3 * point.2) * matrix) ∂realSpecialLinearHaar
          ∂realPlaneUnitMeasure := by
      simp [principalPlaneDomain_periodic_integral_translate function periodic]
    _ = ∫ matrix in principalPlaneDomain, ∫ point : ℝ × ℝ,
        function (realSpecialPlane (3 * point.1) (3 * point.2) * matrix) ∂realPlaneUnitMeasure
          ∂realSpecialLinearHaar := integral_integral_swap joint_integrable
    _ = 0 := by simp only [average_zero, integral_zero]

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
