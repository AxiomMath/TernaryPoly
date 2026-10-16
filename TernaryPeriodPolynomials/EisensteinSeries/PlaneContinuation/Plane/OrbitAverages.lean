module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Plane.UnipotentCharts
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.ShearedPeriodization

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.PlaneFlagCharts TernaryPeriodPolynomials.PlaneEisensteinContinuation.PlaneUnipotentCharts TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspVectors

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.PlaneOrbitAverages

variable {degree : ℕ} {data : InducingData degree} {parameter : ℂ} {function : AdelicGL → ℂ}

def affineKernel (induced : IsInduced data .plane parameter function) (point : AdelicGL) (slope : ℚ)
    (first second : Adeles) : ℂ :=
  data.cusp.realize (planeCuspVector induced (affine (rationalAdele slope) first * point)) (binaryUnipotent second)

def verticalKernel (induced : IsInduced data .plane parameter function) (point : AdelicGL)
    (first second : Adeles) : ℂ :=
  data.cusp.realize (planeCuspVector induced (vertical first * point)) (binaryUnipotent second)

theorem affine_average (induced : IsInduced data .plane parameter function) (point : AdelicGL) (slope : ℚ) (first : Adeles) :
    (∫ second in additiveDomain, affineKernel induced point slope first second ∂adeleMeasure) = 0 :=
  affine_average_zero induced point _ first

theorem vertical_average (induced : IsInduced data .plane parameter function) (point : AdelicGL) (first : Adeles) :
    (∫ second in additiveDomain, verticalKernel induced point first second ∂adeleMeasure) = 0 :=
  vertical_average_zero induced point first

theorem affine_summand {sectionFunction : ℂ → AdelicGL → ℂ}
    (induced : IsInduced data .plane parameter (sectionFunction parameter))
    (point : AdelicGL) (slope shift : ℚ) (first second : Adeles) :
    eisensteinSummand sectionFunction parameter (planeUnipotent first second * point) (flag (.affine slope shift)) =
      affineKernel induced point slope (rationalAdele shift + first + rationalAdele slope * second) second := by
  rw [summand_chart induced]
  change sectionFunction parameter (rationalGroup (affine slope shift) * (planeUnipotent first second * point)) = _
  rw [show rationalGroup (affine slope shift) = affine (rationalAdele slope) (rationalAdele shift) from
    affine_map rationalAdele slope shift, ← mul_assoc, affine_value induced]
  rfl

theorem vertical_summand {sectionFunction : ℂ → AdelicGL → ℂ}
    (induced : IsInduced data .plane parameter (sectionFunction parameter))
    (point : AdelicGL) (shift : ℚ) (first second : Adeles) :
    eisensteinSummand sectionFunction parameter (planeUnipotent first second * point) (flag (.vertical shift)) =
      verticalKernel induced point (rationalAdele shift + second) first := by
  rw [summand_chart induced]
  change sectionFunction parameter (rationalGroup (vertical shift) * (planeUnipotent first second * point)) = _
  rw [show rationalGroup (vertical shift) = vertical (rationalAdele shift) from
    vertical_map rationalAdele shift, ← mul_assoc, vertical_value induced]
  rfl

theorem affine_integral_zero {sectionFunction : ℂ → AdelicGL → ℂ}
    (induced : IsInduced data .plane parameter (sectionFunction parameter))
    (point : AdelicGL) (slope : ℚ)
    (integrable : Integrable (fun pair : Adeles × Adeles => affineKernel induced point slope pair.2 pair.1)
      ((adeleMeasure.restrict additiveDomain).prod adeleMeasure)) :
    (∫ second in additiveDomain, ∫ first in additiveDomain, ∑' shift : ℚ,
      eisensteinSummand sectionFunction parameter (planeUnipotent first second * point) (flag (.affine slope shift))
      ∂adeleMeasure ∂adeleMeasure) = 0 := by
  simp only [affine_summand induced]
  exact ShearedPeriodization.integral_zero (affineKernel induced point slope)
    (fun second => rationalAdele slope * second) integrable (affine_average induced point slope)

theorem vertical_integral_zero {sectionFunction : ℂ → AdelicGL → ℂ}
    (induced : IsInduced data .plane parameter (sectionFunction parameter))
    (point : AdelicGL)
    (integrable : Integrable (fun pair : Adeles × Adeles => verticalKernel induced point pair.2 pair.1)
      ((adeleMeasure.restrict additiveDomain).prod adeleMeasure)) :
    (∫ first in additiveDomain, ∫ second in additiveDomain, ∑' shift : ℚ,
      eisensteinSummand sectionFunction parameter (planeUnipotent first second * point) (flag (.vertical shift))
      ∂adeleMeasure ∂adeleMeasure) = 0 := by
  simp only [vertical_summand induced]
  simpa only [add_zero] using ShearedPeriodization.integral_zero (verticalKernel induced point)
    (fun _ => 0) integrable (vertical_average induced point)

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.PlaneOrbitAverages
