module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Integral.HeightMinimum

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem real_orthogonal_inverse_transpose (matrix : RealGL3)
    (orthogonal : matrix.val.transpose * matrix.val = 1) : matrix.inv = matrix.val.transpose := by
  calc
    matrix.inv = (matrix.val.transpose * matrix.val) * matrix.inv := by rw [orthogonal, one_mul]
    _ = matrix.val.transpose := by rw [mul_assoc, matrix.val_inv, mul_one]

theorem realPlaneHeight_orthogonal_right (matrix rotation : RealGL3)
    (orthogonal : rotation.val.transpose * rotation.val = 1) :
    realPlaneHeight (matrix * rotation) = realPlaneHeight matrix := by
  have reversed : rotation.val * rotation.val.transpose = 1 := by
    rw [← real_orthogonal_inverse_transpose rotation orthogonal]
    exact rotation.val_inv
  have gram : (matrix * rotation).val * (matrix * rotation).val.transpose =
      matrix.val * matrix.val.transpose := by
    change (matrix.val * rotation.val) * (matrix.val * rotation.val).transpose = _
    rw [Matrix.transpose_mul, mul_assoc, ← mul_assoc rotation.val, reversed, one_mul]
  have diagonal := congrArg (fun gram : Matrix (Fin 3) (Fin 3) ℝ => gram 2 2) gram
  have squares : realPlaneHeight (matrix * rotation) ^ 2 = realPlaneHeight matrix ^ 2 := by
    rw [realPlaneHeight_sq, realPlaneHeight_sq]
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three, pow_two] using diagonal
  nlinarith [realPlaneHeight_pos (matrix * rotation), realPlaneHeight_pos matrix]

theorem integral_plane_height_minimum_translate (matrix : RealGL3) (integral : IntegralGL3)
    (minimal : ∀ other : IntegralGL3, realPlaneHeight (integralRealGroup integral * matrix) ≤
      realPlaneHeight (integralRealGroup other * matrix)) :
    ∀ other : IntegralGL3, realPlaneHeight (integralRealGroup integral * matrix) ≤
      realPlaneHeight (integralRealGroup other * (integralRealGroup integral * matrix)) := by
  intro other
  simpa only [map_mul, mul_assoc] using minimal (other * integral)

theorem integral_plane_height_minimum_rotate (matrix rotation : RealGL3)
    (orthogonal : rotation.val.transpose * rotation.val = 1)
    (minimal : ∀ integral : IntegralGL3,
      realPlaneHeight matrix ≤ realPlaneHeight (integralRealGroup integral * matrix)) :
    ∀ integral : IntegralGL3, realPlaneHeight (matrix * rotation) ≤
      realPlaneHeight (integralRealGroup integral * (matrix * rotation)) := by
  intro integral
  rw [← mul_assoc, realPlaneHeight_orthogonal_right _ _ orthogonal,
    realPlaneHeight_orthogonal_right _ _ orthogonal]
  exact minimal integral

theorem integral_real_plane_minimal_decomposition (matrix : RealGL3) :
    ∃ integral : IntegralGL3, ∃ rotation : RealGL3,
      rotation.val.transpose * rotation.val = 1 ∧
      InPlaneParabolic (integralRealGroup integral * matrix * rotation) ∧
      0 < (integralRealGroup integral * matrix * rotation).val 2 2 ∧
      ∀ other : IntegralGL3,
        realPlaneHeight (integralRealGroup integral * matrix * rotation) ≤
          realPlaneHeight (integralRealGroup other * (integralRealGroup integral * matrix * rotation)) := by
  obtain ⟨integral, minimal⟩ := integral_plane_height_minimum_univ matrix
  obtain ⟨rotation, orthogonal, parabolic, height⟩ := real_plane_rotation (integralRealGroup integral * matrix)
  refine ⟨integral, rotation, orthogonal, parabolic, ?_, ?_⟩
  · rw [height]
    exact realPlaneHeight_pos _
  · exact integral_plane_height_minimum_rotate _ _ orthogonal
      (integral_plane_height_minimum_translate matrix integral minimal)

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
