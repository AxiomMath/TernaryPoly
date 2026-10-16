module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Scalar.CuspDecay

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

noncomputable def binaryComplexUnit (value : ℂ) (nonzero : value ≠ 0) : BinaryRealGL :=
  GeneralLinearGroup.mkOfDetNeZero (binaryComplexMatrix value)
    (by rw [binaryComplexMatrix_det]; exact (Complex.normSq_pos.mpr nonzero).ne')

theorem binaryComplexUnit_val (value : ℂ) (nonzero : value ≠ 0) :
    (binaryComplexUnit value nonzero).val = binaryComplexMatrix value := rfl

noncomputable def binaryComplexPhase (value : ℂ) (nonzero : value ≠ 0) : Circle :=
  ⟨value / (‖value‖ : ℂ), by
    change value / (‖value‖ : ℂ) ∈ Metric.sphere 0 1
    rw [Metric.mem_sphere, dist_zero_right]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg value),
      div_self (norm_ne_zero_iff.mpr nonzero)]⟩

theorem binaryComplexUnit_polar (value : ℂ) (nonzero : value ≠ 0) :
    binaryComplexUnit value nonzero =
      GeneralLinearGroup.scalar (Fin 2) (Units.mk0 ‖value‖ (norm_ne_zero_iff.mpr nonzero)) *
        binaryCircleRotation (binaryComplexPhase value nonzero) := by
  apply Units.ext
  rw [binaryComplexUnit_val, Units.val_mul, binaryCircleRotation_val]
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [binaryComplexMatrix, binaryComplexPhase, GeneralLinearGroup.coe_scalar,
      Matrix.scalar_apply, Matrix.mul_apply, Fin.sum_univ_two, Complex.div_ofReal_re,
      Complex.div_ofReal_im] <;> field_simp

theorem binaryUpperHalfPoint_factor (matrix : BinaryRealGL)
    (positive : 0 < (GeneralLinearGroup.det matrix : ℝ)) (point : UpperHalfPlane) :
    matrix * binaryUpperHalfPoint point =
      binaryUpperHalfPoint (matrix • point : UpperHalfPlane) *
        binaryComplexUnit (starRingEnd ℂ (UpperHalfPlane.denom matrix point))
          ((map_ne_zero (starRingEnd ℂ)).mpr (UpperHalfPlane.denom_ne_zero matrix point)) := by
  have identity : (matrix • point : UpperHalfPlane).coe * UpperHalfPlane.denom matrix point =
      UpperHalfPlane.num matrix point := by
    rw [UpperHalfPlane.coe_smul_of_det_pos positive, div_mul_cancel₀ _ (UpperHalfPlane.denom_ne_zero matrix point)]
  have real_part := congrArg Complex.re identity
  have imaginary_part := congrArg Complex.im identity
  simp only [Complex.mul_re, Complex.mul_im, UpperHalfPlane.denom, UpperHalfPlane.num,
    Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.add_im, Complex.mul_im, zero_mul, sub_zero, add_zero] at real_part imaginary_part
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, binaryUpperHalfPoint_val _ point.im_pos,
    binaryUpperHalfPoint_val _ (matrix • point : UpperHalfPlane).im_pos, binaryComplexUnit_val]
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [binaryUpperHalfMatrix, binaryComplexMatrix, UpperHalfPlane.denom,
      Matrix.mul_apply, Fin.sum_univ_two, Complex.mul_re, Complex.mul_im]
  · simpa only [UpperHalfPlane.coe_im, UpperHalfPlane.coe_re, add_comm] using imaginary_part.symm
  · simpa only [UpperHalfPlane.coe_im, UpperHalfPlane.coe_re, sub_eq_add_neg, add_comm] using real_part.symm

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
