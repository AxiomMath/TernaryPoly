module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Plane.ChartContinuity

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.PlaneFlagCharts TernaryPeriodPolynomials.PlaneEisensteinContinuation.PlaneUnipotentCharts

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspidalSectionRelations

structure Relations (function : AdelicGL → ℂ) : Prop where
  rational : ∀ element : planeParabolic ℚ, ∀ point,
    function (rationalGroup element.val * point) = function point
  unipotent : ∀ first second point, function (planeUnipotent first second * point) = function point
  cuspidal : ∀ point, (∫ value in additiveDomain,
    function (planeLevi (binaryUnipotent value) 1 * point) ∂adeleMeasure) = 0

theorem of_induced {degree : ℕ} {data : InducingData degree} {parameter : ℂ} {function : AdelicGL → ℂ}
    (induced : IsInduced data .plane parameter function) : Relations function := by
  refine ⟨RationalInvariance.induced_rational_plane induced, induced.2.2.2.1, ?_⟩
  intro point
  simp only [induced_unipotent induced]
  simpa only [mul_one] using (data.cusp.cuspidal (TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspVectors.planeCuspVector induced point) 1).2

theorem eq_of_flag {function : AdelicGL → ℂ} (relations : Relations function)
    (first second : RationalGL3)
    (sameFlag : (QuotientGroup.mk first : Flags .plane) = QuotientGroup.mk second) (point : AdelicGL) :
    function (rationalGroup first⁻¹ * point) = function (rationalGroup second⁻¹ * point) := by
  have membership : first⁻¹ * second ∈ planeParabolic ℚ := QuotientGroup.eq.mp sameFlag
  have equality := relations.rational ⟨first⁻¹ * second, membership⟩ (rationalGroup second⁻¹ * point)
  change function (rationalGroup (first⁻¹ * second) * (rationalGroup second⁻¹ * point)) = _ at equality
  rw [← mul_assoc, ← map_mul, mul_inv_cancel_right] at equality
  exact equality

theorem summand_chart {sectionFunction : ℂ → AdelicGL → ℂ} {parameter : ℂ}
    (relations : Relations (sectionFunction parameter)) (point : AdelicGL) (chart : Chart) :
    eisensteinSummand sectionFunction parameter point (flag chart) =
      sectionFunction parameter (rationalGroup (representative chart) * point) := by
  have equality : (QuotientGroup.mk (flag chart).out : Flags .plane) =
      QuotientGroup.mk (representative chart)⁻¹ := QuotientGroup.out_eq' _
  simpa only [eisensteinSummand, inv_inv] using eq_of_flag relations _ _ equality point

theorem summand_origin {sectionFunction : ℂ → AdelicGL → ℂ} {parameter : ℂ}
    (relations : Relations (sectionFunction parameter)) (point : AdelicGL) (first second : Adeles) :
    eisensteinSummand sectionFunction parameter (planeUnipotent first second * point) (flag .origin) =
      sectionFunction parameter point := by
  rw [summand_chart relations, representative, map_one, one_mul]
  exact relations.unipotent first second point

def affineKernel (function : AdelicGL → ℂ) (point : AdelicGL) (slope : ℚ) (first second : Adeles) : ℂ :=
  function (planeLevi (binaryUnipotent second) 1 * (affine (rationalAdele slope) first * point))

def verticalKernel (function : AdelicGL → ℂ) (point : AdelicGL) (first second : Adeles) : ℂ :=
  function (planeLevi (binaryUnipotent second) 1 * (vertical first * point))

theorem affine_average {function : AdelicGL → ℂ} (relations : Relations function)
    (point : AdelicGL) (slope : ℚ) (first : Adeles) :
    (∫ second in additiveDomain, affineKernel function point slope first second ∂adeleMeasure) = 0 :=
  relations.cuspidal _

theorem vertical_average {function : AdelicGL → ℂ} (relations : Relations function)
    (point : AdelicGL) (first : Adeles) :
    (∫ second in additiveDomain, verticalKernel function point first second ∂adeleMeasure) = 0 :=
  relations.cuspidal _

theorem affine_summand {sectionFunction : ℂ → AdelicGL → ℂ} {parameter : ℂ}
    (relations : Relations (sectionFunction parameter)) (point : AdelicGL) (slope shift : ℚ) (first second : Adeles) :
    eisensteinSummand sectionFunction parameter (planeUnipotent first second * point) (flag (.affine slope shift)) =
      affineKernel (sectionFunction parameter) point slope (rationalAdele shift + first + rationalAdele slope * second) second := by
  rw [summand_chart relations]
  change sectionFunction parameter (rationalGroup (affine slope shift) * (planeUnipotent first second * point)) = _
  rw [show rationalGroup (affine slope shift) = affine (rationalAdele slope) (rationalAdele shift) from
    affine_map rationalAdele slope shift, ← mul_assoc, affine_action, mul_assoc]
  rfl

theorem vertical_summand {sectionFunction : ℂ → AdelicGL → ℂ} {parameter : ℂ}
    (relations : Relations (sectionFunction parameter)) (point : AdelicGL) (shift : ℚ) (first second : Adeles) :
    eisensteinSummand sectionFunction parameter (planeUnipotent first second * point) (flag (.vertical shift)) =
      verticalKernel (sectionFunction parameter) point (rationalAdele shift + second) first := by
  rw [summand_chart relations]
  change sectionFunction parameter (rationalGroup (vertical shift) * (planeUnipotent first second * point)) = _
  rw [show rationalGroup (vertical shift) = vertical (rationalAdele shift) from
    vertical_map rationalAdele shift, ← mul_assoc, vertical_action, mul_assoc]
  rfl

theorem affineKernel_continuous {function : AdelicGL → ℂ} (continuous : Continuous function)
    (point : AdelicGL) (slope : ℚ) :
    Continuous (fun pair : Adeles × Adeles => affineKernel function point slope pair.2 pair.1) :=
  continuous.comp ((PlaneChartContinuity.leviUnipotent_continuous.comp continuous_fst).mul
    ((PlaneChartContinuity.affine_continuous.comp (continuous_const.prodMk continuous_snd)).mul continuous_const))

theorem verticalKernel_continuous {function : AdelicGL → ℂ} (continuous : Continuous function) (point : AdelicGL) :
    Continuous (fun pair : Adeles × Adeles => verticalKernel function point pair.2 pair.1) :=
  continuous.comp ((PlaneChartContinuity.leviUnipotent_continuous.comp continuous_fst).mul
    ((PlaneChartContinuity.vertical_continuous.comp continuous_snd).mul continuous_const))

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspidalSectionRelations
