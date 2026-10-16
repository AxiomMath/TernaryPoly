module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Scalar.MatrixOrbit

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

noncomputable def binaryConjugatedRotationPath (matrix : BinaryRealGL) (parameter : ℝ) : BinaryRealGL :=
  matrix⁻¹ * binaryRotationPath parameter * matrix

theorem binaryConjugatedRotationPath_zero (matrix : BinaryRealGL) : binaryConjugatedRotationPath matrix 0 = 1 := by
  simp [binaryConjugatedRotationPath, binaryRotationPath_zero]

theorem binaryConjugatedRotationPath_hasDerivAt (matrix : BinaryRealGL) :
    HasDerivAt (fun parameter => (binaryConjugatedRotationPath matrix parameter).val)
      (matrix.inv * binaryRotationDirection * matrix.val) 0 := by
  have rotation : HasDerivAt (fun parameter => (binaryRotationPath parameter).val) binaryRotationDirection 0 :=
    hasDerivAt_pi.mpr (fun row => hasDerivAt_pi.mpr (binaryRotationPath_entry_hasDerivAt_zero row))
  exact (binaryConjugationMap matrix).hasFDerivAt.comp_hasDerivAt 0 rotation

theorem binaryConjugatedRotationPath_entry_hasDerivAt (matrix : BinaryRealGL) (row column : Fin 2) :
    HasDerivAt (fun parameter => (binaryConjugatedRotationPath matrix parameter).val row column)
      ((matrix.inv * binaryRotationDirection * matrix.val) row column) 0 :=
  hasDerivAt_pi.mp (hasDerivAt_pi.mp (binaryConjugatedRotationPath_hasDerivAt matrix) row) column

theorem cuspScalarMatrixOrbit_fderiv_conjugate_rotation (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (argument : BinaryAdelicGL) (matrix : BinaryRealGL) :
    fderiv ℝ (cuspScalarMatrixOrbit cusp vector argument) 1 (matrix.inv * binaryRotationDirection * matrix.val) =
      cusp.realize (cuspDerivedAction cusp (matrix.inv * binaryRotationDirection * matrix.val) vector) argument := by
  have chart := cuspScalarMatrixOrbit_path_hasDerivAt cusp vector argument (binaryConjugatedRotationPath matrix)
    (matrix.inv * binaryRotationDirection * matrix.val) 0 (binaryConjugatedRotationPath_zero matrix)
    (binaryConjugatedRotationPath_entry_hasDerivAt matrix)
  have rotated := cusp_realize_rotation_hasDerivAt cusp (cuspSmoothAction cusp (atInfinity matrix) vector)
    (argument * atInfinity matrix⁻¹) 0
  simp only [binaryRotationPath_zero, binary_atInfinity_one, mul_one] at rotated
  have value : cusp.realize (cuspRotationOperator cusp (cuspSmoothAction cusp (atInfinity matrix) vector))
      (argument * atInfinity matrix⁻¹) =
        cusp.realize (cuspDerivedAction cusp (matrix.inv * binaryRotationDirection * matrix.val) vector) argument := by
    change cusp.realize (cuspDerivedAction cusp binaryRotationDirection (cuspSmoothAction cusp (atInfinity matrix) vector)) _ = _
    rw [cuspDerivedAction_real_covariance]
    change cusp.realize ⟨_, _⟩ _ = _
    rw [cusp.equivariant]
    have cancel : argument * atInfinity matrix⁻¹ * atInfinity matrix = argument := by
      rw [mul_assoc, ← binary_atInfinity_mul, inv_mul_cancel, binary_atInfinity_one, mul_one]
    rw [cancel]
  rw [value] at rotated
  have functions : (fun parameter => cusp.realize vector (argument * atInfinity (binaryConjugatedRotationPath matrix parameter))) =
      (fun parameter => cusp.realize (cuspSmoothAction cusp (atInfinity matrix) vector)
        ((argument * atInfinity matrix⁻¹) * atInfinity (binaryRotationPath parameter))) := by
    funext parameter
    change _ = cusp.realize ⟨_, _⟩ _
    rw [cusp.equivariant]
    simp only [binaryConjugatedRotationPath, binary_atInfinity_mul, mul_assoc]
  rw [functions] at chart
  exact chart.unique rotated

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
