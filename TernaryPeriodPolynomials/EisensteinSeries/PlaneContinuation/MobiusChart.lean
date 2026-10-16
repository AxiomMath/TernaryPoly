module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.CircleCharacters

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.UpperTriangularChart TernaryPeriodPolynomials.PlaneEisensteinContinuation.CircleCharacters TernaryPeriodPolynomials.PlaneEisensteinContinuation.HighestWeightHolomorphic

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.MobiusChart

theorem numerator_relation (matrix : BinaryRealGL)
    (positive : 0 < (Matrix.GeneralLinearGroup.det matrix).val) (argument : UpperHalfPlane) :
    ((matrix • argument : UpperHalfPlane) : ℂ) * UpperHalfPlane.denom matrix argument =
      UpperHalfPlane.num matrix argument := by
  rw [UpperHalfPlane.coe_smul_of_det_pos positive, div_mul_cancel₀ _ (UpperHalfPlane.denom_ne_zero matrix argument)]

/-- The denominator of the Möbius transformation is the exact rotation-and-scale factor. -/
theorem chart_factor (matrix : BinaryRealGL)
    (positive : 0 < (Matrix.GeneralLinearGroup.det matrix).val) (argument : UpperHalfPlane) :
    matrix * unit argument argument.im_pos =
      unit (matrix • argument : UpperHalfPlane) (matrix • argument).im_pos *
        complexUnit (UpperHalfPlane.denom matrix argument) (UpperHalfPlane.denom_ne_zero matrix argument) := by
  have realEquality := congrArg Complex.re (numerator_relation matrix positive argument)
  have imaginaryEquality := congrArg Complex.im (numerator_relation matrix positive argument)
  simp only [Complex.mul_re, Complex.mul_im, UpperHalfPlane.num, UpperHalfPlane.denom,
    Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero, add_zero] at realEquality imaginaryEquality
  change (matrix • argument).re * (matrix.val 1 0 * argument.re + matrix.val 1 1) -
    (matrix • argument).im * (matrix.val 1 0 * argument.im) = matrix.val 0 0 * argument.re + matrix.val 0 1 at realEquality
  change (matrix • argument).re * (matrix.val 1 0 * argument.im) +
    (matrix • argument).im * (matrix.val 1 0 * argument.re + matrix.val 1 1) = matrix.val 0 0 * argument.im at imaginaryEquality
  apply Units.ext
  change matrix.val * UpperTriangularChart.matrix argument =
    UpperTriangularChart.matrix (matrix • argument : UpperHalfPlane) *
      RotationCircle.complexMatrix (UpperHalfPlane.denom matrix argument)
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [UpperTriangularChart.matrix, RotationCircle.complexMatrix, UpperHalfPlane.denom,
      Matrix.mul_apply, Fin.sum_univ_two]
  · linarith [imaginaryEquality]
  · linarith [realEquality]

theorem imaginary_ratio (matrix : BinaryRealGL)
    (positive : 0 < (Matrix.GeneralLinearGroup.det matrix).val) (argument : UpperHalfPlane) :
    (matrix • argument).im = (Matrix.GeneralLinearGroup.det matrix).val * argument.im /
      ‖UpperHalfPlane.denom matrix argument‖ ^ 2 := by
  rw [UpperHalfPlane.im_smul_eq_div_normSq, abs_of_pos positive, Complex.sq_norm]

theorem raw_transform {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth) (index : ℤ)
    (eigen : TernaryPeriodPolynomials.PlaneEisensteinContinuation.LieOperators.rotationOperator data.cusp vector = (Complex.I * index) • vector)
    (point : BinaryAdelicGL) (matrix : BinaryRealGL)
    (positive : 0 < (Matrix.GeneralLinearGroup.det matrix).val) (argument : UpperHalfPlane) :
    raw data.cusp (point * atInfinity matrix) vector argument =
      (UpperHalfPlane.denom matrix argument / (‖UpperHalfPlane.denom matrix argument‖ : ℂ)) ^ index *
        raw data.cusp point vector (matrix • argument : UpperHalfPlane) := by
  rw [raw_eq data.cusp (point * atInfinity matrix) vector argument argument.im_pos,
    mul_assoc, ← Height.atInfinity_mul, chart_factor matrix positive argument,
    Height.atInfinity_mul, ← mul_assoc, realize_complexUnit data vector index eigen,
    raw_eq data.cusp point vector (matrix • argument : UpperHalfPlane) (matrix • argument).im_pos]

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.MobiusChart
