module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Scalar.UpperHalfAction

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

theorem complex_conjugate_phase (value : ℂ) (nonzero : value ≠ 0) :
    starRingEnd ℂ value / (‖value‖ : ℂ) = (‖value‖ : ℂ) / value := by
  have norm_nonzero : (‖value‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr nonzero
  apply (div_eq_div_iff norm_nonzero nonzero).mpr
  rw [mul_comm (starRingEnd ℂ value), Complex.mul_conj', pow_two]

theorem upperHalf_weight_denominator (weight : ℕ) (height : ℝ) (positive : 0 < height)
    (value : ℂ) (nonzero : value ≠ 0) :
    ((height ^ (-(weight : ℝ) / 2) : ℝ) : ℂ) *
        (starRingEnd ℂ value / (‖value‖ : ℂ)) ^ weight =
      (((height / ‖value‖ ^ 2) ^ (-(weight : ℝ) / 2) : ℝ) : ℂ) * value ^ (-(weight : ℤ)) := by
  have power : (‖value‖ ^ 2 : ℝ) ^ (-(weight : ℝ) / 2) = (‖value‖ ^ weight)⁻¹ := by
    rw [← Real.rpow_natCast_mul (norm_nonneg value)]
    have exponent : (2 : ℝ) * (-(weight : ℝ) / 2) = -(weight : ℝ) := by ring
    rw [Nat.cast_ofNat, exponent, Real.rpow_neg (norm_nonneg value), Real.rpow_natCast]
  rw [complex_conjugate_phase value nonzero, Real.div_rpow positive.le (sq_nonneg _), power,
    div_inv_eq_mul, Complex.ofReal_mul, Complex.ofReal_pow, _root_.zpow_neg, zpow_natCast, div_pow]
  ring

theorem cohomological_upperHalfForm_transform {cusp : CuspidalRepresentation} {degree : ℕ}
    (cohomological : Cohomological cusp degree) (weight : ℕ) (vector : cusp.smooth)
    (rotation : cuspRotationOperator cusp vector = (Complex.I * (weight : ℂ)) • vector)
    (argument : BinaryAdelicGL) (matrix : BinaryRealGL)
    (determinant : (GeneralLinearGroup.det matrix : ℝ) = 1) (point : UpperHalfPlane) :
    cuspUpperHalfForm cusp weight vector (argument * atInfinity matrix) point =
      cuspUpperHalfForm cusp weight vector argument (matrix • point) *
        UpperHalfPlane.denom matrix point ^ (-(weight : ℤ)) := by
  have positive : 0 < (GeneralLinearGroup.det matrix : ℝ) := by rw [determinant]; norm_num
  have height : (matrix • point : UpperHalfPlane).im =
      point.im / ‖UpperHalfPlane.denom matrix point‖ ^ 2 := by
    rw [UpperHalfPlane.im_smul_eq_div_normSq, determinant, abs_one, one_mul, Complex.sq_norm]
  simp only [cuspUpperHalfForm, cuspHolomorphicFunction]
  rw [cohomological_upperHalfOrbit_action cohomological weight vector rotation argument matrix positive point]
  simp only [Complex.real_smul, UpperHalfPlane.coe_im]
  calc
    _ = (((point.im ^ (-(weight : ℝ) / 2) : ℝ) : ℂ) *
        (starRingEnd ℂ (UpperHalfPlane.denom matrix point) / (‖UpperHalfPlane.denom matrix point‖ : ℂ)) ^ weight) *
          cuspUpperHalfOrbit cusp vector argument (matrix • point : UpperHalfPlane) := by ring
    _ = _ := by
      rw [upperHalf_weight_denominator weight point.im point.im_pos _ (UpperHalfPlane.denom_ne_zero matrix point),
        ← height]
      ring

theorem cohomological_upperHalfForm_slash {cusp : CuspidalRepresentation} {degree : ℕ}
    (cohomological : Cohomological cusp degree) (weight : ℕ) (vector : cusp.smooth)
    (rotation : cuspRotationOperator cusp vector = (Complex.I * (weight : ℂ)) • vector)
    (argument : BinaryAdelicGL) (matrix : BinaryRealGL)
    (determinant : (GeneralLinearGroup.det matrix : ℝ) = 1) :
    SlashAction.map (weight : ℤ) matrix (cuspUpperHalfForm cusp weight vector argument) =
      cuspUpperHalfForm cusp weight vector (argument * atInfinity matrix) := by
  funext point
  rw [ModularForm.slash_apply]
  have conjugation (value : ℂ) : UpperHalfPlane.σ matrix value = value := by
    simp [UpperHalfPlane.σ, determinant]
  simp only [conjugation, determinant, abs_one, Complex.ofReal_one, _root_.one_zpow, mul_one]
  exact (cohomological_upperHalfForm_transform cohomological weight vector rotation argument matrix determinant point).symm

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
