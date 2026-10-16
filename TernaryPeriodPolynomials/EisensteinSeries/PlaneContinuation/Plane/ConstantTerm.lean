module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Plane.OrbitAverages
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Plane.FlagSeries
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.SeriesIntegrability
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Scalar.Series

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.PlaneFlagCharts TernaryPeriodPolynomials.PlaneEisensteinContinuation.PlaneUnipotentCharts TernaryPeriodPolynomials.PlaneEisensteinContinuation.PlaneOrbitAverages

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.PlaneConstantTerm

instance flagCountable : Countable (Flags .plane) := Function.Surjective.countable flag_surjective

def parameterMeasure : Measure (Adeles × Adeles) :=
  (adeleMeasure.restrict additiveDomain).prod (adeleMeasure.restrict additiveDomain)

instance parameterProbability : IsProbabilityMeasure parameterMeasure := by
  let _ : IsProbabilityMeasure (adeleMeasure.restrict additiveDomain) :=
    ⟨by rw [Measure.restrict_apply_univ, TernaryPeriodPolynomials.PlaneEisensteinContinuation.Norm.adeleMeasure_additiveDomain]⟩
  exact inferInstanceAs (IsProbabilityMeasure
    ((adeleMeasure.restrict additiveDomain).prod (adeleMeasure.restrict additiveDomain)))

def term (sectionFunction : ℂ → AdelicGL → ℂ) (parameter : ℂ) (point : AdelicGL) (flag : Flags .plane)
    (pair : Adeles × Adeles) : ℂ :=
  eisensteinSummand sectionFunction parameter (planeUnipotent pair.1 pair.2 * point) flag

def average (function : AdelicGL → ℂ) (point : AdelicGL) : ℂ :=
  ∫ pair, function (planeUnipotent pair.1 pair.2 * point) ∂parameterMeasure

variable {degree : ℕ} {data : InducingData degree} {parameter : ℂ} {sectionFunction : ℂ → AdelicGL → ℂ}
variable (induced : IsInduced data .plane parameter (sectionFunction parameter)) (point : AdelicGL)

include induced

theorem origin_integral :
    (∫ pair, term sectionFunction parameter point (flag .origin) pair ∂parameterMeasure) = sectionFunction parameter point := by
  simp only [term, summand_origin induced, integral_const, probReal_univ, one_smul]

theorem affine_sum_zero (slope : ℚ)
    (integrable : ∀ flag, Integrable (term sectionFunction parameter point flag) parameterMeasure)
    (summable : Summable (fun flag => ∫ pair, ‖term sectionFunction parameter point flag pair‖ ∂parameterMeasure))
    (kernelIntegrable : Integrable (fun pair : Adeles × Adeles => affineKernel induced point slope pair.2 pair.1)
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
  exact (integral_prod_symm _ orbitIntegrable).trans (affine_integral_zero induced point slope kernelIntegrable)

theorem vertical_sum_zero
    (integrable : ∀ flag, Integrable (term sectionFunction parameter point flag) parameterMeasure)
    (summable : Summable (fun flag => ∫ pair, ‖term sectionFunction parameter point flag pair‖ ∂parameterMeasure))
    (kernelIntegrable : Integrable (fun pair : Adeles × Adeles => verticalKernel induced point pair.2 pair.1)
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
  exact (integral_prod _ orbitIntegrable).trans (vertical_integral_zero induced point kernelIntegrable)

theorem average_literalSum
    (integrable : ∀ flag, Integrable (term sectionFunction parameter point flag) parameterMeasure)
    (summable : Summable (fun flag => ∫ pair, ‖term sectionFunction parameter point flag pair‖ ∂parameterMeasure))
    (affineIntegrable : ∀ slope : ℚ,
      Integrable (fun pair : Adeles × Adeles => affineKernel induced point slope pair.2 pair.1)
        ((adeleMeasure.restrict additiveDomain).prod adeleMeasure))
    (verticalIntegrable : Integrable (fun pair : Adeles × Adeles => verticalKernel induced point pair.2 pair.1)
      ((adeleMeasure.restrict additiveDomain).prod adeleMeasure)) :
    average (ScalarSeries.literalSum sectionFunction parameter) point = sectionFunction parameter point := by
  have summed := hasSum_integral_of_summable_integral_norm integrable summable
  change (∫ pair, ∑' flag, term sectionFunction parameter point flag pair ∂parameterMeasure) = _
  rw [← summed.tsum_eq, PlaneFlagSeries.tsum_flags _ summed.summable, origin_integral induced point,
    vertical_sum_zero induced point integrable summable verticalIntegrable]
  simp only [affine_sum_zero induced point _ integrable summable (affineIntegrable _), tsum_zero, add_zero]

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.PlaneConstantTerm
