module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.CuspidalSectionRelations
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.UnipotentCompactDomain

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.PlaneFlagCharts TernaryPeriodPolynomials.PlaneEisensteinContinuation.PlaneConstantTerm TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspidalSectionRelations

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspidalConstantTerm

variable {parameter : ℂ} {sectionFunction : ℂ → AdelicGL → ℂ}
variable (relations : Relations (sectionFunction parameter)) (point : AdelicGL)

include relations

theorem affine_integral_zero (slope : ℚ)
    (integrable : Integrable (fun pair : Adeles × Adeles => affineKernel (sectionFunction parameter) point slope pair.2 pair.1)
      ((adeleMeasure.restrict additiveDomain).prod adeleMeasure)) :
    (∫ second in additiveDomain, ∫ first in additiveDomain, ∑' shift : ℚ,
      eisensteinSummand sectionFunction parameter (planeUnipotent first second * point) (flag (.affine slope shift))
      ∂adeleMeasure ∂adeleMeasure) = 0 := by
  simp only [affine_summand relations]
  exact ShearedPeriodization.integral_zero (affineKernel (sectionFunction parameter) point slope)
    (fun second => rationalAdele slope * second) integrable (affine_average relations point slope)

theorem vertical_integral_zero
    (integrable : Integrable (fun pair : Adeles × Adeles => verticalKernel (sectionFunction parameter) point pair.2 pair.1)
      ((adeleMeasure.restrict additiveDomain).prod adeleMeasure)) :
    (∫ first in additiveDomain, ∫ second in additiveDomain, ∑' shift : ℚ,
      eisensteinSummand sectionFunction parameter (planeUnipotent first second * point) (flag (.vertical shift))
      ∂adeleMeasure ∂adeleMeasure) = 0 := by
  simp only [vertical_summand relations]
  simpa only [add_zero] using ShearedPeriodization.integral_zero (verticalKernel (sectionFunction parameter) point)
    (fun _ => 0) integrable (vertical_average relations point)

theorem origin_integral :
    (∫ pair, term sectionFunction parameter point (flag .origin) pair ∂parameterMeasure) = sectionFunction parameter point := by
  simp only [term, summand_origin relations, integral_const, probReal_univ, one_smul]

theorem affine_sum_zero (slope : ℚ)
    (integrable : ∀ flag, Integrable (term sectionFunction parameter point flag) parameterMeasure)
    (summable : Summable (fun flag => ∫ pair, ‖term sectionFunction parameter point flag pair‖ ∂parameterMeasure))
    (kernelIntegrable : Integrable (fun pair : Adeles × Adeles => affineKernel (sectionFunction parameter) point slope pair.2 pair.1)
      ((adeleMeasure.restrict additiveDomain).prod adeleMeasure)) :
    (∑' shift : ℚ, ∫ pair, term sectionFunction parameter point (flag (.affine slope shift)) pair ∂parameterMeasure) = 0 := by
  have injective : Function.Injective (fun shift => flag (.affine slope shift)) := by
    intro first second equality
    exact (Chart.affine.inj (flag_injective equality)).2
  have orbitSummable := summable.comp_injective injective
  have orbitIntegrable := SeriesIntegrability.tsum_integrable
    (fun shift => term sectionFunction parameter point (flag (.affine slope shift)))
    (fun shift => integrable _) orbitSummable
  rw [integral_tsum_of_summable_integral_norm (fun shift => integrable (flag (.affine slope shift))) orbitSummable]
  exact (integral_prod_symm _ orbitIntegrable).trans (affine_integral_zero relations point slope kernelIntegrable)

theorem vertical_sum_zero
    (integrable : ∀ flag, Integrable (term sectionFunction parameter point flag) parameterMeasure)
    (summable : Summable (fun flag => ∫ pair, ‖term sectionFunction parameter point flag pair‖ ∂parameterMeasure))
    (kernelIntegrable : Integrable (fun pair : Adeles × Adeles => verticalKernel (sectionFunction parameter) point pair.2 pair.1)
      ((adeleMeasure.restrict additiveDomain).prod adeleMeasure)) :
    (∑' shift : ℚ, ∫ pair, term sectionFunction parameter point (flag (.vertical shift)) pair ∂parameterMeasure) = 0 := by
  have injective : Function.Injective (fun shift => flag (.vertical shift)) := by
    intro first second equality
    exact Chart.vertical.inj (flag_injective equality)
  have orbitSummable := summable.comp_injective injective
  have orbitIntegrable := SeriesIntegrability.tsum_integrable
    (fun shift => term sectionFunction parameter point (flag (.vertical shift)))
    (fun shift => integrable _) orbitSummable
  rw [integral_tsum_of_summable_integral_norm (fun shift => integrable (flag (.vertical shift))) orbitSummable]
  exact (integral_prod _ orbitIntegrable).trans (vertical_integral_zero relations point kernelIntegrable)

theorem average_with_orbit_integrability
    (integrable : ∀ flag, Integrable (term sectionFunction parameter point flag) parameterMeasure)
    (summable : Summable (fun flag => ∫ pair, ‖term sectionFunction parameter point flag pair‖ ∂parameterMeasure))
    (affineIntegrable : ∀ slope : ℚ,
      Integrable (fun pair : Adeles × Adeles => affineKernel (sectionFunction parameter) point slope pair.2 pair.1)
        ((adeleMeasure.restrict additiveDomain).prod adeleMeasure))
    (verticalIntegrable : Integrable (fun pair : Adeles × Adeles => verticalKernel (sectionFunction parameter) point pair.2 pair.1)
      ((adeleMeasure.restrict additiveDomain).prod adeleMeasure)) :
    average (ScalarSeries.literalSum sectionFunction parameter) point = sectionFunction parameter point := by
  have summed := hasSum_integral_of_summable_integral_norm integrable summable
  change (∫ pair, ∑' flag, term sectionFunction parameter point flag pair ∂parameterMeasure) = _
  rw [← summed.tsum_eq, PlaneFlagSeries.tsum_flags _ summed.summable, origin_integral relations point,
    vertical_sum_zero relations point integrable summable verticalIntegrable]
  simp only [affine_sum_zero relations point _ integrable summable (affineIntegrable _), tsum_zero, add_zero]

theorem affine_integrable (slope : ℚ)
    (measurable : Measurable (fun pair : Adeles × Adeles => affineKernel (sectionFunction parameter) point slope pair.2 pair.1))
    (integrable : ∀ flag, Integrable (term sectionFunction parameter point flag) parameterMeasure)
    (summable : Summable (fun flag => ∫ pair, ‖term sectionFunction parameter point flag pair‖ ∂parameterMeasure)) :
    Integrable (fun pair : Adeles × Adeles => affineKernel (sectionFunction parameter) point slope pair.2 pair.1)
      ((adeleMeasure.restrict additiveDomain).prod adeleMeasure) := by
  have injective : Function.Injective (fun shift => flag (.affine slope shift)) := by
    intro first second equality
    exact (Chart.affine.inj (flag_injective equality)).2
  have orbitSummable := summable.comp_injective injective
  have bound : (∫⁻ pair, ∑' shift : ℚ,
      ‖term sectionFunction parameter point (flag (.affine slope shift)) pair‖ₑ ∂parameterMeasure) < ⊤ := by
    rw [lintegral_tsum (fun shift => (integrable (flag (.affine slope shift))).aestronglyMeasurable.enorm)]
    exact SeriesIntegrability.sum_lintegral_lt_top _ (fun shift => integrable _) orbitSummable
  apply ShearedPeriodization.integrable_of_periodized_bound (affineKernel (sectionFunction parameter) point slope) measurable
    (fun second => rationalAdele slope * second)
  have equality := lintegral_prod_symm (fun pair : Adeles × Adeles =>
    ∑' shift : ℚ, ‖term sectionFunction parameter point (flag (.affine slope shift)) pair‖ₑ)
    (AEMeasurable.tsum (fun shift => (integrable (flag (.affine slope shift))).aestronglyMeasurable.enorm))
  change (∫⁻ pair, ∑' shift : ℚ,
    ‖term sectionFunction parameter point (flag (.affine slope shift)) pair‖ₑ ∂parameterMeasure) = _ at equality
  rw [equality] at bound
  simpa only [term, affine_summand relations] using bound

theorem vertical_integrable
    (measurable : Measurable (fun pair : Adeles × Adeles => verticalKernel (sectionFunction parameter) point pair.2 pair.1))
    (integrable : ∀ flag, Integrable (term sectionFunction parameter point flag) parameterMeasure)
    (summable : Summable (fun flag => ∫ pair, ‖term sectionFunction parameter point flag pair‖ ∂parameterMeasure)) :
    Integrable (fun pair : Adeles × Adeles => verticalKernel (sectionFunction parameter) point pair.2 pair.1)
      ((adeleMeasure.restrict additiveDomain).prod adeleMeasure) := by
  have injective : Function.Injective (fun shift => flag (.vertical shift)) := by
    intro first second equality
    exact Chart.vertical.inj (flag_injective equality)
  have orbitSummable := summable.comp_injective injective
  have bound : (∫⁻ pair, ∑' shift : ℚ,
      ‖term sectionFunction parameter point (flag (.vertical shift)) pair‖ₑ ∂parameterMeasure) < ⊤ := by
    rw [lintegral_tsum (fun shift => (integrable (flag (.vertical shift))).aestronglyMeasurable.enorm)]
    exact SeriesIntegrability.sum_lintegral_lt_top _ (fun shift => integrable _) orbitSummable
  apply ShearedPeriodization.integrable_of_periodized_bound (verticalKernel (sectionFunction parameter) point) measurable (fun _ => 0)
  have equality := lintegral_prod (fun pair : Adeles × Adeles =>
    ∑' shift : ℚ, ‖term sectionFunction parameter point (flag (.vertical shift)) pair‖ₑ)
    (AEMeasurable.tsum (fun shift => (integrable (flag (.vertical shift))).aestronglyMeasurable.enorm))
  change (∫⁻ pair, ∑' shift : ℚ,
    ‖term sectionFunction parameter point (flag (.vertical shift)) pair‖ₑ ∂parameterMeasure) = _ at equality
  rw [equality] at bound
  simpa only [term, vertical_summand relations, add_zero] using bound

theorem average_literalSum
    (affineMeasurable : ∀ slope : ℚ,
      Measurable (fun pair : Adeles × Adeles => affineKernel (sectionFunction parameter) point slope pair.2 pair.1))
    (verticalMeasurable : Measurable (fun pair : Adeles × Adeles => verticalKernel (sectionFunction parameter) point pair.2 pair.1))
    (integrable : ∀ flag, Integrable (term sectionFunction parameter point flag) parameterMeasure)
    (summable : Summable (fun flag => ∫ pair, ‖term sectionFunction parameter point flag pair‖ ∂parameterMeasure)) :
    average (ScalarSeries.literalSum sectionFunction parameter) point = sectionFunction parameter point :=
  average_with_orbit_integrability relations point integrable summable
    (fun slope => affine_integrable relations point slope (affineMeasurable slope) integrable summable)
    (vertical_integrable relations point verticalMeasurable integrable summable)

theorem average_of_integral_norm (continuous : Continuous (sectionFunction parameter))
    (summable : Summable (fun flag => ∫ pair, ‖term sectionFunction parameter point flag pair‖ ∂parameterMeasure)) :
    average (ScalarSeries.literalSum sectionFunction parameter) point = sectionFunction parameter point := by
  apply average_literalSum relations point
    (fun slope => (affineKernel_continuous continuous point slope).measurable)
    (verticalKernel_continuous continuous point).measurable
    _ summable
  intro flag
  exact UnipotentCompactDomain.continuous_integrable _
    (continuous.comp (continuous_const.mul (PlaneChartContinuity.planeUnipotent_continuous.mul continuous_const)))

theorem average_of_majorant (continuous : Continuous (sectionFunction parameter))
    (majorant : Flags .plane → ℝ) (summable : Summable majorant)
    (bounded : ∀ pair ∈ additiveDomain ×ˢ additiveDomain, ∀ flag,
      ‖term sectionFunction parameter point flag pair‖ ≤ majorant flag) :
    average (ScalarSeries.literalSum sectionFunction parameter) point = sectionFunction parameter point := by
  apply average_of_integral_norm relations point continuous
  apply summable.of_nonneg_of_le (fun flag => integral_nonneg (fun pair => norm_nonneg _))
  intro flag
  have termIntegrable : Integrable (term sectionFunction parameter point flag) parameterMeasure :=
    UnipotentCompactDomain.continuous_integrable _
      (continuous.comp (continuous_const.mul (PlaneChartContinuity.planeUnipotent_continuous.mul continuous_const)))
  have boundIntegral := integral_mono_ae termIntegrable.norm
    (integrable_const (μ := parameterMeasure) (majorant flag))
    (UnipotentCompactDomain.ae_mem_domain.mono (fun pair membership => bounded pair membership flag))
  simpa only [integral_const, probReal_univ, one_smul] using boundIntegral

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspidalConstantTerm
