module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Plane.OrbitIntegrability
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Induced.Continuity

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.PlaneFlagCharts TernaryPeriodPolynomials.PlaneEisensteinContinuation.PlaneUnipotentCharts TernaryPeriodPolynomials.PlaneEisensteinContinuation.PlaneOrbitAverages
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.PlaneConstantTerm

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.PlaneChartContinuity

theorem affine_continuous {Ring : Type*} [CommRing Ring] [TopologicalSpace Ring] [IsTopologicalRing Ring] :
    Continuous (fun pair : Ring × Ring => affine pair.1 pair.2) := by
  apply Units.continuous_iff.mpr
  constructor <;> apply continuous_pi <;> intro row <;> apply continuous_pi <;> intro column <;>
    fin_cases row <;> fin_cases column <;> simp only [affine] <;> fun_prop

theorem vertical_continuous {Ring : Type*} [CommRing Ring] [TopologicalSpace Ring] [IsTopologicalRing Ring] :
    Continuous (vertical (Ring := Ring)) := by
  apply Units.continuous_iff.mpr
  constructor <;> apply continuous_pi <;> intro row <;> apply continuous_pi <;> intro column <;>
    fin_cases row <;> fin_cases column <;> simp only [vertical] <;> fun_prop

theorem leviUnipotent_continuous {Ring : Type*} [CommRing Ring] [TopologicalSpace Ring] [IsTopologicalRing Ring] :
    Continuous (fun value : Ring => planeLevi (binaryUnipotent value) 1) := by
  apply Units.continuous_iff.mpr
  constructor <;> apply continuous_pi <;> intro row <;> apply continuous_pi <;> intro column <;>
    fin_cases row <;> fin_cases column <;> simp only [planeLevi, planeBlock, binaryUnipotent] <;> fun_prop

theorem planeUnipotent_continuous {Ring : Type*} [CommRing Ring] [TopologicalSpace Ring] [IsTopologicalRing Ring] :
    Continuous (fun pair : Ring × Ring => planeUnipotent pair.1 pair.2) := by
  apply Units.continuous_iff.mpr
  constructor <;> apply continuous_pi <;> intro row <;> apply continuous_pi <;> intro column <;>
    fin_cases row <;> fin_cases column <;> simp only [planeUnipotent] <;> fun_prop

variable {degree : ℕ} {data : InducingData degree} {parameter : ℂ} {sectionFunction : ℂ → AdelicGL → ℂ}
variable (induced : IsInduced data .plane parameter (sectionFunction parameter)) (point : AdelicGL)

include induced

theorem affineKernel_continuous (slope : ℚ) :
    Continuous (fun pair : Adeles × Adeles => affineKernel induced point slope pair.2 pair.1) := by
  have result : Continuous (fun pair : Adeles × Adeles => sectionFunction parameter
      (planeLevi (binaryUnipotent pair.1) 1 * (affine (rationalAdele slope) pair.2 * point))) :=
    (InducedContinuity.continuous induced).comp ((leviUnipotent_continuous.comp continuous_fst).mul
      ((affine_continuous.comp (continuous_const.prodMk continuous_snd)).mul continuous_const))
  exact result.congr (fun pair => induced_unipotent induced _ _)

theorem verticalKernel_continuous :
    Continuous (fun pair : Adeles × Adeles => verticalKernel induced point pair.2 pair.1) := by
  have result : Continuous (fun pair : Adeles × Adeles => sectionFunction parameter
      (planeLevi (binaryUnipotent pair.1) 1 * (vertical pair.2 * point))) :=
    (InducedContinuity.continuous induced).comp ((leviUnipotent_continuous.comp continuous_fst).mul
      ((vertical_continuous.comp continuous_snd).mul continuous_const))
  exact result.congr (fun pair => induced_unipotent induced _ _)

theorem term_continuous (flag : Flags .plane) : Continuous (term sectionFunction parameter point flag) :=
  (InducedContinuity.continuous induced).comp
    (continuous_const.mul (planeUnipotent_continuous.mul continuous_const))

theorem average_literalSum
    (integrable : ∀ flag, Integrable (term sectionFunction parameter point flag) parameterMeasure)
    (summable : Summable (fun flag => ∫ pair, ‖term sectionFunction parameter point flag pair‖ ∂parameterMeasure)) :
    average (ScalarSeries.literalSum sectionFunction parameter) point = sectionFunction parameter point :=
  PlaneOrbitIntegrability.average_literalSum induced point
    (fun slope => (affineKernel_continuous induced point slope).measurable)
    (verticalKernel_continuous induced point).measurable integrable summable

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.PlaneChartContinuity
