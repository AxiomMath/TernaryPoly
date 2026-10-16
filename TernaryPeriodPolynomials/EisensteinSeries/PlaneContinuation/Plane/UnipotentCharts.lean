module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Plane.FlagCharts
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Rational.Invariance
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Singular.Cuspidality

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.PlaneFlagCharts TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspVectors

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.PlaneUnipotentCharts

theorem affine_action {Ring : Type*} [CommRing Ring] (slope shift first second : Ring) :
    affine slope shift * planeUnipotent first second =
      planeLevi (binaryUnipotent second) 1 * affine slope (shift + first + slope * second) := by
  apply Units.ext
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [affine, planeUnipotent, planeLevi, planeBlock, binaryUnipotent, Matrix.mul_apply, Fin.sum_univ_three]
  ring

theorem vertical_action {Ring : Type*} [CommRing Ring] (shift first second : Ring) :
    vertical shift * planeUnipotent first second =
      planeLevi (binaryUnipotent first) 1 * vertical (shift + second) := by
  apply Units.ext
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [vertical, planeUnipotent, planeLevi, planeBlock, binaryUnipotent, Matrix.mul_apply, Fin.sum_univ_three]
  ring

theorem binaryUnipotent_det {Ring : Type*} [CommRing Ring] (parameter : Ring) :
    GeneralLinearGroup.det (binaryUnipotent parameter) = 1 := by
  apply Units.ext
  simp [GeneralLinearGroup.val_det_apply, binaryUnipotent, Matrix.det_fin_two]

theorem induced_unipotent {degree : ℕ} {data : InducingData degree} {parameter : ℂ} {function : AdelicGL → ℂ}
    (induced : IsInduced data .plane parameter function) (point : AdelicGL) (value : Adeles) :
    function (planeLevi (binaryUnipotent value) 1 * point) =
      data.cusp.realize (planeCuspVector induced point) (binaryUnipotent value) := by
  rw [induced_eq_planeCuspVector induced, binaryUnipotent_det, TernaryPeriodPolynomials.PlaneEisensteinContinuation.Helpers.normPower_one, one_mul]

theorem affine_value {degree : ℕ} {data : InducingData degree} {parameter : ℂ} {function : AdelicGL → ℂ}
    (induced : IsInduced data .plane parameter function) (point : AdelicGL) (slope shift first second : Adeles) :
    function (affine slope shift * planeUnipotent first second * point) =
      data.cusp.realize (planeCuspVector induced (affine slope (shift + first + slope * second) * point))
        (binaryUnipotent second) := by
  rw [affine_action, mul_assoc, induced_unipotent induced]

theorem vertical_value {degree : ℕ} {data : InducingData degree} {parameter : ℂ} {function : AdelicGL → ℂ}
    (induced : IsInduced data .plane parameter function) (point : AdelicGL) (shift first second : Adeles) :
    function (vertical shift * planeUnipotent first second * point) =
      data.cusp.realize (planeCuspVector induced (vertical (shift + second) * point))
        (binaryUnipotent first) := by
  rw [vertical_action, mul_assoc, induced_unipotent induced]

theorem summand_chart {degree : ℕ} {data : InducingData degree} {parameter : ℂ}
    {sectionFunction : ℂ → AdelicGL → ℂ}
    (induced : IsInduced data .plane parameter (sectionFunction parameter)) (point : AdelicGL) (chart : Chart) :
    eisensteinSummand sectionFunction parameter point (flag chart) =
      sectionFunction parameter (rationalGroup (representative chart) * point) := by
  have equality : (QuotientGroup.mk (flag chart).out : Flags .plane) =
      QuotientGroup.mk (representative chart)⁻¹ := QuotientGroup.out_eq' _
  simpa only [eisensteinSummand, inv_inv] using
    RationalInvariance.induced_eq_of_flag induced _ _ equality point

theorem summand_origin {degree : ℕ} {data : InducingData degree} {parameter : ℂ}
    {sectionFunction : ℂ → AdelicGL → ℂ}
    (induced : IsInduced data .plane parameter (sectionFunction parameter)) (point : AdelicGL) (first second : Adeles) :
    eisensteinSummand sectionFunction parameter (planeUnipotent first second * point) (flag .origin) =
      sectionFunction parameter point := by
  rw [summand_chart induced, representative, map_one, one_mul]
  exact induced.2.2.2.1 first second point

theorem affine_average_zero {degree : ℕ} {data : InducingData degree} {parameter : ℂ} {function : AdelicGL → ℂ}
    (induced : IsInduced data .plane parameter function) (point : AdelicGL) (slope shift : Adeles) :
    (∫ value in additiveDomain, data.cusp.realize (planeCuspVector induced (affine slope shift * point))
      (binaryUnipotent value) ∂adeleMeasure) = 0 := by
  simpa only [mul_one] using (data.cusp.cuspidal (planeCuspVector induced (affine slope shift * point)) 1).2

theorem vertical_average_zero {degree : ℕ} {data : InducingData degree} {parameter : ℂ} {function : AdelicGL → ℂ}
    (induced : IsInduced data .plane parameter function) (point : AdelicGL) (shift : Adeles) :
    (∫ value in additiveDomain, data.cusp.realize (planeCuspVector induced (vertical shift * point))
      (binaryUnipotent value) ∂adeleMeasure) = 0 := by
  simpa only [mul_one] using (data.cusp.cuspidal (planeCuspVector induced (vertical shift * point)) 1).2

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.PlaneUnipotentCharts
