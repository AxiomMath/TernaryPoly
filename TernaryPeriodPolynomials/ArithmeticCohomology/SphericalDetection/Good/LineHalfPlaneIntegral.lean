module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Good.LineHalfPlaneJacobian

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def goodLineFirstCoordinateMap (real : ℝ × ℝ) : ℝ × ℝ :=
  (-real.2 * real.1 / (real.1 ^ 2 + 1), real.2 / (real.1 ^ 2 + 1))

theorem goodLineHalfPlaneCoordinateMap_inverse (point : ℝ × ℝ) (pivot : point.2 ≠ 0) :
    goodLineFirstCoordinateMap (goodLineHalfPlaneCoordinateMap point) = point := by
  have square_nonzero : point.1 ^ 2 + point.2 ^ 2 ≠ 0 := ne_of_gt (by nlinarith [sq_pos_of_ne_zero pivot])
  apply Prod.ext <;>
    simp only [goodLineFirstCoordinateMap, goodLineHalfPlaneCoordinateMap] <;>
    field_simp

theorem goodLineFirstCoordinateMap_inverse (real : ℝ × ℝ) (pivot : real.2 ≠ 0) :
    goodLineHalfPlaneCoordinateMap (goodLineFirstCoordinateMap real) = real := by
  have denominator : real.1 ^ 2 + 1 ≠ 0 := ne_of_gt (by positivity)
  apply Prod.ext <;>
    simp only [goodLineFirstCoordinateMap, goodLineHalfPlaneCoordinateMap] <;>
    field_simp

theorem goodLineHalfPlaneCoordinateMap_positive (point : ℝ × ℝ) (positive : 0 < point.2) :
    0 < (goodLineHalfPlaneCoordinateMap point).2 := by
  change 0 < (point.1 ^ 2 + point.2 ^ 2) / point.2
  exact div_pos (by nlinarith [sq_nonneg point.1]) positive

theorem goodLineFirstCoordinateMap_positive (real : ℝ × ℝ) (positive : 0 < real.2) :
    0 < (goodLineFirstCoordinateMap real).2 := by
  change 0 < real.2 / (real.1 ^ 2 + 1)
  positivity

theorem goodLineHalfPlaneCoordinateMap_bijOn :
    Set.BijOn goodLineHalfPlaneCoordinateMap {point : ℝ × ℝ | 0 < point.2} {point : ℝ × ℝ | 0 < point.2} := by
  refine ⟨fun point positive => goodLineHalfPlaneCoordinateMap_positive point positive, ?_, ?_⟩
  · intro first first_positive second second_positive equality
    have inverse := congrArg goodLineFirstCoordinateMap equality
    rwa [goodLineHalfPlaneCoordinateMap_inverse first (ne_of_gt first_positive),
      goodLineHalfPlaneCoordinateMap_inverse second (ne_of_gt second_positive)] at inverse
  · intro real positive
    exact ⟨goodLineFirstCoordinateMap real, goodLineFirstCoordinateMap_positive real positive,
      goodLineFirstCoordinateMap_inverse real (ne_of_gt positive)⟩

theorem integral_goodLineHalfPlaneCoordinateMap {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (integrand : (ℝ × ℝ) → F) :
    ∫ real in {point : ℝ × ℝ | 0 < point.2}, integrand real ∂((volume : Measure ℝ).prod volume) =
      ∫ point in {point : ℝ × ℝ | 0 < point.2},
        ((point.1 ^ 2 + point.2 ^ 2) / point.2 ^ 3) • integrand (goodLineHalfPlaneCoordinateMap point)
        ∂((volume : Measure ℝ).prod volume) := by
  have measurable : MeasurableSet {point : ℝ × ℝ | 0 < point.2} :=
    isOpen_lt continuous_const continuous_snd |>.measurableSet
  have equality := integral_image_eq_integral_abs_det_fderiv_smul ((volume : Measure ℝ).prod volume)
    measurable (fun point positive => (goodLineHalfPlaneCoordinateMap_hasFDerivAt point
      (ne_of_gt positive)).hasFDerivWithinAt) goodLineHalfPlaneCoordinateMap_bijOn.injOn integrand
  rw [goodLineHalfPlaneCoordinateMap_bijOn.image_eq] at equality
  rw [equality]
  apply setIntegral_congr_fun measurable
  intro point positive
  exact congrArg (fun scalar : ℝ => scalar • integrand (goodLineHalfPlaneCoordinateMap point))
    (goodLineHalfPlaneCoordinateDerivative_abs_det point positive)

end TernaryPeriodPolynomials.SphericalDetection.Helpers
