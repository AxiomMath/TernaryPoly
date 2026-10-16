module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Good.LineHalfPlaneIntegral
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Good.LineFirstProjectionRegularity

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem goodLineHalfPlaneCoordinateDerivative_abs_det_nonzero (point : ℝ × ℝ) (pivot : point.2 ≠ 0) :
    |(goodLineHalfPlaneCoordinateDerivative point).det| = (point.1 ^ 2 + point.2 ^ 2) / |point.2| ^ 3 := by
  rw [goodLineHalfPlaneCoordinateDerivative_det point pivot, neg_div, abs_neg, abs_div, abs_pow,
    abs_of_nonneg (by positivity : 0 ≤ point.1 ^ 2 + point.2 ^ 2)]

theorem goodLineHalfPlaneCoordinateMap_bijOn_nonzero :
    Set.BijOn goodLineHalfPlaneCoordinateMap {point : ℝ × ℝ | point.2 ≠ 0}
      {point : ℝ × ℝ | point.2 ≠ 0} := by
  refine ⟨?_, ?_, ?_⟩
  · intro point pivot
    change (point.1 ^ 2 + point.2 ^ 2) / point.2 ≠ 0
    exact div_ne_zero (ne_of_gt (by nlinarith [sq_pos_of_ne_zero pivot])) pivot
  · intro first first_pivot second second_pivot equality
    have inverse := congrArg goodLineFirstCoordinateMap equality
    rwa [goodLineHalfPlaneCoordinateMap_inverse first first_pivot,
      goodLineHalfPlaneCoordinateMap_inverse second second_pivot] at inverse
  · intro real pivot
    refine ⟨goodLineFirstCoordinateMap real, ?_, goodLineFirstCoordinateMap_inverse real pivot⟩
    change real.2 / (real.1 ^ 2 + 1) ≠ 0
    exact div_ne_zero pivot (ne_of_gt (by positivity))

theorem goodLinePlane_second_ne_zero_ae :
    ∀ᵐ point : ℝ × ℝ ∂((volume : Measure ℝ).prod volume), point.2 ≠ 0 := by
  rw [ae_iff]
  simpa using affinePlaneZero_measure 0 1 0 (Or.inr (Or.inl one_ne_zero))

theorem integral_goodLinePlaneCoordinateMap {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (integrand : (ℝ × ℝ) → F) :
    ∫ real : ℝ × ℝ, integrand real ∂((volume : Measure ℝ).prod volume) =
      ∫ point : ℝ × ℝ, ((point.1 ^ 2 + point.2 ^ 2) / |point.2| ^ 3) •
        integrand (goodLineHalfPlaneCoordinateMap point) ∂((volume : Measure ℝ).prod volume) := by
  have measurable : MeasurableSet {point : ℝ × ℝ | point.2 ≠ 0} :=
    (isClosed_eq continuous_snd continuous_const).isOpen_compl.measurableSet
  have equality := integral_image_eq_integral_abs_det_fderiv_smul ((volume : Measure ℝ).prod volume)
    measurable (fun point pivot => (goodLineHalfPlaneCoordinateMap_hasFDerivAt point pivot).hasFDerivWithinAt)
      goodLineHalfPlaneCoordinateMap_bijOn_nonzero.injOn integrand
  rw [goodLineHalfPlaneCoordinateMap_bijOn_nonzero.image_eq] at equality
  have restrict (function : (ℝ × ℝ) → F) :
      ∫ point in {point : ℝ × ℝ | point.2 ≠ 0}, function point ∂((volume : Measure ℝ).prod volume) =
        ∫ point : ℝ × ℝ, function point ∂((volume : Measure ℝ).prod volume) := by
    apply setIntegral_eq_integral_of_ae_compl_eq_zero
    filter_upwards [goodLinePlane_second_ne_zero_ae] with point pivot
    exact fun outside => False.elim (outside pivot)
  rw [restrict, restrict] at equality
  rw [equality]
  apply integral_congr_ae
  filter_upwards [goodLinePlane_second_ne_zero_ae] with point pivot
  exact congrArg (fun scalar : ℝ => scalar • integrand (goodLineHalfPlaneCoordinateMap point))
    (goodLineHalfPlaneCoordinateDerivative_abs_det_nonzero point pivot)

end TernaryPeriodPolynomials.SphericalDetection.Helpers
