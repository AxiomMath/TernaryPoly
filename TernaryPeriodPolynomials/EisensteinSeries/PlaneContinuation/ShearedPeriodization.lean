module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Rational.AdditiveDomain
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.AdditiveIntegration

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory
open scoped TernaryPeriodPolynomials.PlaneEisensteinContinuation.RationalAdditiveDomain
open scoped ENNReal

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.ShearedPeriodization

theorem lintegral_eq (function : Adeles → Adeles → ℝ≥0∞)
    (measurable : ∀ second, Measurable (fun first => function first second)) (shift : Adeles → Adeles) :
    (∫⁻ second in additiveDomain, ∫⁻ first in additiveDomain,
      ∑' rational : ℚ, function (rationalAdele rational + first + shift second) second ∂adeleMeasure ∂adeleMeasure) =
        ∫⁻ second in additiveDomain, ∫⁻ first, function first second ∂adeleMeasure ∂adeleMeasure := by
  apply lintegral_congr
  intro second
  have termMeasurable (rational : ℚ) :
      Measurable (fun first : Adeles => function (rationalAdele rational + first + shift second) second) :=
    (measurable second).comp ((measurable_const.add measurable_id).add measurable_const)
  rw [lintegral_tsum (fun rational => (termMeasurable rational).aemeasurable)]
  have unfoldIntegral := RationalAdditiveDomain.domain_fundamental.lintegral_eq_tsum''
    (fun first => function (first + shift second) second)
  simp only [RationalAdditiveDomain.rational_vadd] at unfoldIntegral
  rw [← unfoldIntegral]
  exact lintegral_add_right_eq_self (fun first => function first second) (shift second)

theorem integrable_of_periodized_bound (function : Adeles → Adeles → ℂ)
    (measurable : Measurable (fun pair : Adeles × Adeles => function pair.2 pair.1))
    (shift : Adeles → Adeles)
    (bounded : (∫⁻ second in additiveDomain, ∫⁻ first in additiveDomain,
      ∑' rational : ℚ, ‖function (rationalAdele rational + first + shift second) second‖ₑ
        ∂adeleMeasure ∂adeleMeasure) < ⊤) :
    Integrable (fun pair : Adeles × Adeles => function pair.2 pair.1)
      ((adeleMeasure.restrict additiveDomain).prod adeleMeasure) := by
  refine ⟨measurable.aestronglyMeasurable, ?_⟩
  change (∫⁻ pair : Adeles × Adeles, ‖function pair.2 pair.1‖ₑ
    ∂(adeleMeasure.restrict additiveDomain).prod adeleMeasure) < ⊤
  rw [lintegral_prod _ measurable.enorm.aemeasurable]
  rw [← lintegral_eq (fun first second => ‖function first second‖ₑ)
    (fun second => measurable.enorm.comp (measurable_const.prodMk measurable_id)) shift]
  exact bounded

variable {Target : Type*} [NormedAddCommGroup Target] [NormedSpace ℝ Target]

theorem integral_eq (function : Adeles → Adeles → Target) (shift : Adeles → Adeles)
    (integrable : Integrable (fun pair : Adeles × Adeles => function pair.2 pair.1)
      ((adeleMeasure.restrict additiveDomain).prod adeleMeasure)) :
    (∫ second in additiveDomain, ∫ first in additiveDomain,
      ∑' rational : ℚ, function (rationalAdele rational + first + shift second) second ∂adeleMeasure ∂adeleMeasure) =
        ∫ first, ∫ second in additiveDomain, function first second ∂adeleMeasure ∂adeleMeasure := by
  calc
    _ = ∫ second in additiveDomain, ∫ first, function first second ∂adeleMeasure ∂adeleMeasure := by
      apply integral_congr_ae
      filter_upwards [integrable.prod_right_ae] with second integrableSecond
      have unfoldIntegral := AdditiveIntegration.integral_periodization RationalAdditiveDomain.domain_fundamental
        (integrableSecond.comp_add_right (shift second))
      simp only [RationalAdditiveDomain.rational_vadd] at unfoldIntegral
      rw [unfoldIntegral]
      exact integral_add_right_eq_self (fun first => function first second) (shift second)
    _ = _ := integral_integral_swap integrable

theorem integral_zero (function : Adeles → Adeles → Target) (shift : Adeles → Adeles)
    (integrable : Integrable (fun pair : Adeles × Adeles => function pair.2 pair.1)
      ((adeleMeasure.restrict additiveDomain).prod adeleMeasure))
    (vanishing : ∀ first, (∫ second in additiveDomain, function first second ∂adeleMeasure) = 0) :
    (∫ second in additiveDomain, ∫ first in additiveDomain,
      ∑' rational : ℚ, function (rationalAdele rational + first + shift second) second ∂adeleMeasure ∂adeleMeasure) = 0 := by
  rw [integral_eq function shift integrable]
  simp only [vanishing, MeasureTheory.integral_zero]

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.ShearedPeriodization
