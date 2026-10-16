module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Scalar.MatrixDifferential

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

def binaryUpperHalfMatrix (point : ℂ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![point.im, point.re; 0, 1]

noncomputable def binaryUpperHalfTangent : ℂ →L[ℝ] Matrix (Fin 2) (Fin 2) ℝ :=
  ContinuousLinearMap.pi ![ContinuousLinearMap.pi ![Complex.imCLM, Complex.reCLM], 0]

theorem binaryUpperHalfTangent_apply (direction : ℂ) :
    binaryUpperHalfTangent direction = !![direction.im, direction.re; 0, 0] := by
  ext row column
  fin_cases row <;> fin_cases column <;> rfl

theorem binaryUpperHalfMatrix_hasFDerivAt (point : ℂ) :
    HasFDerivAt binaryUpperHalfMatrix binaryUpperHalfTangent point := by
  have expression : binaryUpperHalfMatrix =
      fun point => binaryUpperHalfTangent point + !![0, 0; 0, 1] := by
    funext point
    ext row column
    fin_cases row <;> fin_cases column <;>
      simp [binaryUpperHalfMatrix, binaryUpperHalfTangent_apply]
  rw [expression]
  exact binaryUpperHalfTangent.hasFDerivAt.add_const _

theorem binaryUpperHalfMatrix_det (point : ℂ) : (binaryUpperHalfMatrix point).det = point.im := by
  simp [binaryUpperHalfMatrix, Matrix.det_fin_two]

noncomputable def binaryUpperHalfPoint (point : ℂ) : BinaryRealGL :=
  invertibleMatrix (binaryUpperHalfMatrix point)

theorem binaryUpperHalfPoint_val (point : ℂ) (positive : 0 < point.im) :
    (binaryUpperHalfPoint point).val = binaryUpperHalfMatrix point := by
  simp only [binaryUpperHalfPoint, invertibleMatrix, binaryUpperHalfMatrix_det,
    dite_eq_left positive.ne', GeneralLinearGroup.val_mkOfDetNeZero]

theorem binaryUpperHalfMatrix_real_tangent (point : ℂ) (positive : 0 < point.im) :
    binaryUpperHalfTangent 1 = (binaryUpperHalfPoint point).val *
      ((2 * point.im)⁻¹ • (binarySymmetricDirection + binaryRotationDirection)) := by
  rw [binaryUpperHalfPoint_val point positive, binaryUpperHalfTangent_apply]
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [binaryUpperHalfMatrix, binarySymmetricDirection, binaryRotationDirection,
      Matrix.mul_apply, Fin.sum_univ_two]
  field_simp
  norm_num

theorem binaryUpperHalfMatrix_imaginary_tangent (point : ℂ) (positive : 0 < point.im) :
    binaryUpperHalfTangent Complex.I = (binaryUpperHalfPoint point).val *
      ((2 * point.im)⁻¹ • (binarySplitDirection + 1)) := by
  rw [binaryUpperHalfPoint_val point positive, binaryUpperHalfTangent_apply]
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [binaryUpperHalfMatrix, binarySplitDirection, Matrix.mul_apply, Fin.sum_univ_two]
  field_simp
  norm_num

noncomputable def cuspUpperHalfOrbit (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (argument : BinaryAdelicGL) (point : ℂ) : ℂ :=
  cuspScalarMatrixOrbit cusp vector argument (binaryUpperHalfMatrix point)

theorem cuspUpperHalfOrbit_apply (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (argument : BinaryAdelicGL) (point : ℂ) :
    cuspUpperHalfOrbit cusp vector argument point =
      cusp.realize vector (argument * atInfinity (binaryUpperHalfPoint point)) := rfl

theorem cuspUpperHalfOrbit_hasFDerivAt (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (argument : BinaryAdelicGL) (point : ℂ) (positive : 0 < point.im) :
    HasFDerivAt (cuspUpperHalfOrbit cusp vector argument)
      ((fderiv ℝ (cuspScalarMatrixOrbit cusp vector argument) (binaryUpperHalfMatrix point)).comp
        binaryUpperHalfTangent) point := by
  have smooth := cuspScalarMatrixOrbit_contDiffAt cusp vector argument (binaryUpperHalfPoint point)
  rw [binaryUpperHalfPoint_val point positive] at smooth
  exact (smooth.differentiableAt (by simp)).hasFDerivAt.comp point (binaryUpperHalfMatrix_hasFDerivAt point)

theorem cuspUpperHalfOrbit_fderiv_real (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (argument : BinaryAdelicGL) (point : ℂ) (positive : 0 < point.im) :
    fderiv ℝ (cuspUpperHalfOrbit cusp vector argument) point 1 =
      ((2 * point.im)⁻¹ : ℝ) •
        (cuspUpperHalfOrbit cusp (cuspSymmetricOperator cusp vector) argument point +
          cuspUpperHalfOrbit cusp (cuspRotationOperator cusp vector) argument point) := by
  rw [(cuspUpperHalfOrbit_hasFDerivAt cusp vector argument point positive).fderiv,
    ContinuousLinearMap.comp_apply, binaryUpperHalfMatrix_real_tangent point positive,
    ← binaryUpperHalfPoint_val point positive, cuspScalarMatrixOrbit_left_derivative]
  rw [map_smul, map_add, cuspScalarMatrixOrbit_fderiv_traceless cusp vector _ _
    binary_rankOne_directions_traceless.2.2, cuspScalarMatrixOrbit_fderiv_traceless cusp vector _ _
      binary_rankOne_directions_traceless.1]
  rfl

theorem cohomological_upperHalfOrbit_fderiv_imaginary {cusp : CuspidalRepresentation} {degree : ℕ}
    (cohomological : Cohomological cusp degree) (vector : cusp.smooth)
    (argument : BinaryAdelicGL) (point : ℂ) (positive : 0 < point.im) :
    fderiv ℝ (cuspUpperHalfOrbit cusp vector argument) point Complex.I =
      ((2 * point.im)⁻¹ : ℝ) • cuspUpperHalfOrbit cusp (cuspSplitOperator cusp vector) argument point := by
  rw [(cuspUpperHalfOrbit_hasFDerivAt cusp vector argument point positive).fderiv,
    ContinuousLinearMap.comp_apply, binaryUpperHalfMatrix_imaginary_tangent point positive,
    ← binaryUpperHalfPoint_val point positive, cuspScalarMatrixOrbit_left_derivative,
    map_smul, map_add, cohomological_scalar_fderiv_identity cohomological, add_zero,
    cuspScalarMatrixOrbit_fderiv_traceless cusp vector _ _ binary_rankOne_directions_traceless.2.1]
  rfl

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
