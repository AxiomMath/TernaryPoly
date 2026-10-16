module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Good.LineFirstTransition

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem goodLineFirstProjection_det (real : ℝ × ℝ) (pivot : real.2 ≠ 0) :
    (GeneralLinearGroup.det (realPlaneFirstProjection (standardGoodLineRealArgument real)).right : ℝ) =
      1 / real.2 := by
  change (realPlaneFirstProjection (standardGoodLineRealArgument real)).right.val.det = _
  rw [goodLineFirstProjection_binary real pivot]
  simp [Matrix.det_fin_two, neg_div, one_div]

theorem goodLineFirstProjection_halfPlane (real : ℝ × ℝ) (positive : 0 < real.2) :
    (((realPlaneFirstProjection (standardGoodLineRealArgument real)).right • UpperHalfPlane.I : UpperHalfPlane) : ℂ) =
      -(real.2 : ℂ) / ((real.1 : ℂ) + Complex.I) := by
  have pivot := ne_of_gt positive
  have determinant : (0 : ℝ) < GeneralLinearGroup.det
      (realPlaneFirstProjection (standardGoodLineRealArgument real)).right := by
    rw [goodLineFirstProjection_det real pivot]
    positivity
  rw [UpperHalfPlane.coe_smul_of_det_pos determinant, UpperHalfPlane.coe_I]
  simp only [UpperHalfPlane.num, UpperHalfPlane.denom, goodLineFirstProjection_binary real pivot]
  change ((0 : ℂ) * Complex.I + 1) /
    (((-(1 : ℝ) / real.2 : ℝ) : ℂ) * Complex.I + ((-real.1 / real.2 : ℝ) : ℂ)) = _
  simp only [Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_one, zero_mul, zero_add]
  have denominator : -(1 : ℂ) / (real.2 : ℂ) * Complex.I +
      -(real.1 : ℂ) / (real.2 : ℂ) = -(((real.1 : ℂ) + Complex.I) / (real.2 : ℂ)) := by ring
  rw [denominator, one_div, inv_neg, inv_div, neg_div]

theorem goodLineFirstProjection_halfPlane_coordinates (real : ℝ × ℝ) (positive : 0 < real.2) :
    let point := (realPlaneFirstProjection (standardGoodLineRealArgument real)).right • UpperHalfPlane.I
    point.re = -real.2 * real.1 / (real.1 ^ 2 + 1) ∧
      point.im = real.2 / (real.1 ^ 2 + 1) := by
  change (↑((realPlaneFirstProjection (standardGoodLineRealArgument real)).right • UpperHalfPlane.I) : ℂ).re = _ ∧
    (↑((realPlaneFirstProjection (standardGoodLineRealArgument real)).right • UpperHalfPlane.I) : ℂ).im = _
  rw [goodLineFirstProjection_halfPlane real positive]
  simp [Complex.div_re, Complex.div_im, Complex.normSq_apply, pow_two]
  ring

def goodLineHalfPlaneCoordinates (point : UpperHalfPlane) : ℝ × ℝ :=
  (-point.re / point.im, Complex.normSq (point : ℂ) / point.im)

theorem goodLineHalfPlaneCoordinates_positive (point : UpperHalfPlane) :
    0 < (goodLineHalfPlaneCoordinates point).2 := by
  change 0 < Complex.normSq (point : ℂ) / point.im
  apply div_pos _ point.im_pos
  rw [Complex.normSq_apply]
  change 0 < point.re * point.re + point.im * point.im
  exact add_pos_of_nonneg_of_pos (mul_self_nonneg _) (mul_pos point.im_pos point.im_pos)

theorem goodLineHalfPlaneCoordinates_left_inverse (real : ℝ × ℝ) (positive : 0 < real.2) :
    goodLineHalfPlaneCoordinates
      ((realPlaneFirstProjection (standardGoodLineRealArgument real)).right • UpperHalfPlane.I) = real := by
  obtain ⟨real_part, imaginary_part⟩ := goodLineFirstProjection_halfPlane_coordinates real positive
  have denominator : real.1 ^ 2 + 1 ≠ 0 := ne_of_gt (by positivity)
  have pivot := ne_of_gt positive
  apply Prod.ext
  · change -((realPlaneFirstProjection (standardGoodLineRealArgument real)).right • UpperHalfPlane.I).re /
        ((realPlaneFirstProjection (standardGoodLineRealArgument real)).right • UpperHalfPlane.I).im = real.1
    rw [real_part, imaginary_part]
    field_simp
  · change Complex.normSq (↑((realPlaneFirstProjection (standardGoodLineRealArgument real)).right • UpperHalfPlane.I) : ℂ) /
        ((realPlaneFirstProjection (standardGoodLineRealArgument real)).right • UpperHalfPlane.I).im = real.2
    rw [Complex.normSq_apply]
    change (((realPlaneFirstProjection (standardGoodLineRealArgument real)).right • UpperHalfPlane.I).re *
        ((realPlaneFirstProjection (standardGoodLineRealArgument real)).right • UpperHalfPlane.I).re +
      ((realPlaneFirstProjection (standardGoodLineRealArgument real)).right • UpperHalfPlane.I).im *
        ((realPlaneFirstProjection (standardGoodLineRealArgument real)).right • UpperHalfPlane.I).im) /
        ((realPlaneFirstProjection (standardGoodLineRealArgument real)).right • UpperHalfPlane.I).im = real.2
    rw [real_part, imaginary_part]
    field_simp

theorem goodLineHalfPlaneCoordinates_right_inverse (point : UpperHalfPlane) :
    (realPlaneFirstProjection (standardGoodLineRealArgument (goodLineHalfPlaneCoordinates point))).right •
      UpperHalfPlane.I = point := by
  obtain ⟨real_part, imaginary_part⟩ := goodLineFirstProjection_halfPlane_coordinates
    (goodLineHalfPlaneCoordinates point) (goodLineHalfPlaneCoordinates_positive point)
  have imaginary_nonzero := ne_of_gt point.im_pos
  have square_nonzero : point.re ^ 2 + point.im ^ 2 ≠ 0 := ne_of_gt (by nlinarith [point.im_pos])
  apply UpperHalfPlane.ext
  apply Complex.ext
  · change ((realPlaneFirstProjection (standardGoodLineRealArgument (goodLineHalfPlaneCoordinates point))).right •
        UpperHalfPlane.I).re = point.re
    rw [real_part]
    simp only [goodLineHalfPlaneCoordinates, Complex.normSq_apply, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
    field_simp
  · change ((realPlaneFirstProjection (standardGoodLineRealArgument (goodLineHalfPlaneCoordinates point))).right •
        UpperHalfPlane.I).im = point.im
    rw [imaginary_part]
    simp only [goodLineHalfPlaneCoordinates, Complex.normSq_apply, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
    field_simp

end TernaryPeriodPolynomials.SphericalDetection.Helpers
