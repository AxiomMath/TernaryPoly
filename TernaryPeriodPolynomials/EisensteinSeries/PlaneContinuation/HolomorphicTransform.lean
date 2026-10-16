module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.MobiusChart

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.UpperTriangularChart TernaryPeriodPolynomials.PlaneEisensteinContinuation.HighestWeightHolomorphic TernaryPeriodPolynomials.PlaneEisensteinContinuation.LieOperators

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.HolomorphicTransform

theorem transformed_log (matrix : BinaryRealGL) (determinant : (Matrix.GeneralLinearGroup.det matrix).val = 1)
    (argument : UpperHalfPlane) :
    Real.log (matrix • argument).im = Real.log argument.im - 2 * Real.log ‖UpperHalfPlane.denom matrix argument‖ := by
  have nonzero := norm_ne_zero_iff.mpr (UpperHalfPlane.denom_ne_zero matrix argument)
  rw [MobiusChart.imaginary_ratio matrix (by rw [determinant]; norm_num), determinant, one_mul,
    Real.log_div (ne_of_gt argument.im_pos) (pow_ne_zero 2 nonzero), Real.log_pow]
  norm_num

theorem normalization_transform (weight : ℤ) (matrix : BinaryRealGL)
    (determinant : (Matrix.GeneralLinearGroup.det matrix).val = 1) (argument : UpperHalfPlane) :
    normalization weight (matrix • argument : UpperHalfPlane) =
      (‖UpperHalfPlane.denom matrix argument‖ : ℂ) ^ weight * normalization weight argument := by
  change Complex.exp (-(weight : ℂ) / 2 * (Real.log (matrix • argument).im : ℂ)) = _
  rw [transformed_log matrix determinant argument]
  push_cast
  have exponent : -(weight : ℂ) / 2 * ((Real.log argument.im : ℂ) - 2 * (Real.log ‖UpperHalfPlane.denom matrix argument‖ : ℂ)) =
      (weight : ℂ) * (Real.log ‖UpperHalfPlane.denom matrix argument‖ : ℂ) +
        (-(weight : ℂ) / 2 * (Real.log argument.im : ℂ)) := by ring
  rw [exponent, Complex.exp_add, Complex.exp_int_mul]
  rw [← Complex.ofReal_exp, Real.exp_log (norm_pos_iff.mpr (UpperHalfPlane.denom_ne_zero matrix argument))]
  rfl

/-- The actual normalized scalar realization has the weight-k SL2 transformation law. -/
theorem function_transform {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth) (weight : ℤ)
    (eigen : rotationOperator data.cusp vector = (Complex.I * (-weight : ℤ)) • vector)
    (point : BinaryAdelicGL) (matrix : BinaryRealGL)
    (determinant : (Matrix.GeneralLinearGroup.det matrix).val = 1) (argument : UpperHalfPlane) :
    function data.cusp (point * atInfinity matrix) vector weight argument =
      UpperHalfPlane.denom matrix argument ^ (-weight) *
        function data.cusp point vector weight (matrix • argument : UpperHalfPlane) := by
  rw [function, MobiusChart.raw_transform data vector (-weight) eigen point matrix
    (by rw [determinant]; norm_num) argument]
  rw [function, normalization_transform weight matrix determinant argument]
  rw [div_zpow]
  simp only [zpow_neg]
  simp only [div_eq_mul_inv, inv_inv]
  ring

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.HolomorphicTransform
