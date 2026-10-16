module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Plane.ConstantTerm

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.PlaneFlagCharts TernaryPeriodPolynomials.PlaneEisensteinContinuation.PlaneOrbitAverages TernaryPeriodPolynomials.PlaneEisensteinContinuation.PlaneConstantTerm

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.PlaneOrbitIntegrability

variable {degree : ℕ} {data : InducingData degree} {parameter : ℂ} {sectionFunction : ℂ → AdelicGL → ℂ}
variable (induced : IsInduced data .plane parameter (sectionFunction parameter)) (point : AdelicGL)

theorem affine_integrable (slope : ℚ)
    (measurable : Measurable (fun pair : Adeles × Adeles => affineKernel induced point slope pair.2 pair.1))
    (integrable : ∀ flag, Integrable (term sectionFunction parameter point flag) parameterMeasure)
    (summable : Summable (fun flag => ∫ pair, ‖term sectionFunction parameter point flag pair‖ ∂parameterMeasure)) :
    Integrable (fun pair : Adeles × Adeles => affineKernel induced point slope pair.2 pair.1)
      ((adeleMeasure.restrict additiveDomain).prod adeleMeasure) := by
  have injective : Function.Injective (fun shift => flag (.affine slope shift)) := by
    intro first second equality
    exact (Chart.affine.inj (flag_injective equality)).2
  have orbitSummable := summable.comp_injective injective
  have bound : (∫⁻ pair, ∑' shift : ℚ,
      ‖term sectionFunction parameter point (flag (.affine slope shift)) pair‖ₑ ∂parameterMeasure) < ⊤ := by
    rw [lintegral_tsum (fun shift => (integrable (flag (.affine slope shift))).aestronglyMeasurable.enorm)]
    exact SeriesIntegrability.sum_lintegral_lt_top _ (fun shift => integrable _) orbitSummable
  apply ShearedPeriodization.integrable_of_periodized_bound (affineKernel induced point slope) measurable
    (fun second => rationalAdele slope * second)
  have equality := lintegral_prod_symm (fun pair : Adeles × Adeles =>
    ∑' shift : ℚ, ‖term sectionFunction parameter point (flag (.affine slope shift)) pair‖ₑ)
    (AEMeasurable.tsum (fun shift => (integrable (flag (.affine slope shift))).aestronglyMeasurable.enorm))
  change (∫⁻ pair, ∑' shift : ℚ,
    ‖term sectionFunction parameter point (flag (.affine slope shift)) pair‖ₑ ∂parameterMeasure) = _ at equality
  rw [equality] at bound
  simpa only [term, affine_summand induced] using bound

theorem vertical_integrable
    (measurable : Measurable (fun pair : Adeles × Adeles => verticalKernel induced point pair.2 pair.1))
    (integrable : ∀ flag, Integrable (term sectionFunction parameter point flag) parameterMeasure)
    (summable : Summable (fun flag => ∫ pair, ‖term sectionFunction parameter point flag pair‖ ∂parameterMeasure)) :
    Integrable (fun pair : Adeles × Adeles => verticalKernel induced point pair.2 pair.1)
      ((adeleMeasure.restrict additiveDomain).prod adeleMeasure) := by
  have injective : Function.Injective (fun shift => flag (.vertical shift)) := by
    intro first second equality
    exact Chart.vertical.inj (flag_injective equality)
  have orbitSummable := summable.comp_injective injective
  have bound : (∫⁻ pair, ∑' shift : ℚ,
      ‖term sectionFunction parameter point (flag (.vertical shift)) pair‖ₑ ∂parameterMeasure) < ⊤ := by
    rw [lintegral_tsum (fun shift => (integrable (flag (.vertical shift))).aestronglyMeasurable.enorm)]
    exact SeriesIntegrability.sum_lintegral_lt_top _ (fun shift => integrable _) orbitSummable
  apply ShearedPeriodization.integrable_of_periodized_bound (verticalKernel induced point) measurable (fun _ => 0)
  have equality := lintegral_prod (fun pair : Adeles × Adeles =>
    ∑' shift : ℚ, ‖term sectionFunction parameter point (flag (.vertical shift)) pair‖ₑ)
    (AEMeasurable.tsum (fun shift => (integrable (flag (.vertical shift))).aestronglyMeasurable.enorm))
  change (∫⁻ pair, ∑' shift : ℚ,
    ‖term sectionFunction parameter point (flag (.vertical shift)) pair‖ₑ ∂parameterMeasure) = _ at equality
  rw [equality] at bound
  simpa only [term, vertical_summand induced, add_zero] using bound

theorem average_literalSum
    (affineMeasurable : ∀ slope : ℚ,
      Measurable (fun pair : Adeles × Adeles => affineKernel induced point slope pair.2 pair.1))
    (verticalMeasurable : Measurable (fun pair : Adeles × Adeles => verticalKernel induced point pair.2 pair.1))
    (integrable : ∀ flag, Integrable (term sectionFunction parameter point flag) parameterMeasure)
    (summable : Summable (fun flag => ∫ pair, ‖term sectionFunction parameter point flag pair‖ ∂parameterMeasure)) :
    average (ScalarSeries.literalSum sectionFunction parameter) point = sectionFunction parameter point :=
  PlaneConstantTerm.average_literalSum induced point integrable summable
    (fun slope => affine_integrable induced point slope (affineMeasurable slope) integrable summable)
    (vertical_integrable induced point verticalMeasurable integrable summable)

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.PlaneOrbitIntegrability
