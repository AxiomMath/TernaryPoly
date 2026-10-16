module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Integral.DualHeightMinimum

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

theorem realDualHeight_pos (matrix : RealGL3) : 0 < realDualHeight matrix := realPlaneHeight_pos _

theorem realDualHeight_sq (matrix : RealGL3) :
    realDualHeight matrix ^ 2 = matrix.inv 0 0 ^ 2 + matrix.inv 1 0 ^ 2 + matrix.inv 2 0 ^ 2 := by
  rw [realDualHeight, realPlaneHeight_sq]
  simp [generalLinearInverseTranspose, weyl, Matrix.mul_apply, Fin.sum_univ_three]

theorem real_plane_determinant (matrix : RealGL3) (parabolic : InPlaneParabolic matrix) :
    matrix.val.det = (matrix.val 0 0 * matrix.val 1 1 - matrix.val 0 1 * matrix.val 1 0) * matrix.val 2 2 := by
  simp only [Matrix.det_fin_three, parabolic.1, parabolic.2]
  ring

theorem real_plane_corner_ne_zero (matrix : RealGL3) (parabolic : InPlaneParabolic matrix) :
    matrix.val 2 2 ≠ 0 := by
  intro zero
  apply matrix.det_ne_zero
  rw [real_plane_determinant matrix parabolic, zero, mul_zero]

theorem realDualHeight_projected_row_sq (matrix : RealGL3) (parabolic : InPlaneParabolic matrix) :
    realDualHeight matrix ^ 2 * matrix.val.det ^ 2 =
      matrix.val 2 2 ^ 2 * (matrix.val 1 0 ^ 2 + matrix.val 1 1 ^ 2) := by
  have inverse_parabolic := inPlane_inv parabolic
  have inverse_zero : matrix.inv 2 0 = 0 := inverse_parabolic.1
  have first := congrArg (fun value : Matrix (Fin 3) (Fin 3) ℝ => value 0 0) matrix.val_inv
  have second := congrArg (fun value : Matrix (Fin 3) (Fin 3) ℝ => value 1 0) matrix.val_inv
  simp only [Matrix.mul_apply, Fin.sum_univ_three, inverse_zero, mul_zero, add_zero,
    Matrix.one_apply_eq, Matrix.one_apply_ne (by decide : (1 : Fin 3) ≠ 0)] at first second
  let determinant := matrix.val 0 0 * matrix.val 1 1 - matrix.val 0 1 * matrix.val 1 0
  have first_entry : determinant * matrix.inv 0 0 = matrix.val 1 1 := by
    calc
      _ = matrix.val 1 1 * (matrix.val 0 0 * matrix.inv 0 0 + matrix.val 0 1 * matrix.inv 1 0) -
        matrix.val 0 1 * (matrix.val 1 0 * matrix.inv 0 0 + matrix.val 1 1 * matrix.inv 1 0) := by
          dsimp only [determinant]
          ring
      _ = _ := by rw [first, second]; ring
  have second_entry : determinant * matrix.inv 1 0 = -matrix.val 1 0 := by
    calc
      _ = matrix.val 0 0 * (matrix.val 1 0 * matrix.inv 0 0 + matrix.val 1 1 * matrix.inv 1 0) -
        matrix.val 1 0 * (matrix.val 0 0 * matrix.inv 0 0 + matrix.val 0 1 * matrix.inv 1 0) := by
          dsimp only [determinant]
          ring
      _ = _ := by rw [first, second]; ring
  rw [realDualHeight_sq, inverse_zero, zero_pow (by decide : 2 ≠ 0), add_zero,
    real_plane_determinant matrix parabolic]
  change (matrix.inv 0 0 ^ 2 + matrix.inv 1 0 ^ 2) * (determinant * matrix.val 2 2) ^ 2 = _
  calc
    _ = matrix.val 2 2 ^ 2 * ((determinant * matrix.inv 1 0) ^ 2 +
        (determinant * matrix.inv 0 0) ^ 2) := by ring
    _ = _ := by rw [first_entry, second_entry, neg_sq]

theorem realDualHeight_comparison (first second : RealGL3)
    (first_parabolic : InPlaneParabolic first) (second_parabolic : InPlaneParabolic second)
    (determinants : |first.val.det| = |second.val.det|)
    (corners : first.val 2 2 = second.val 2 2) :
    realDualHeight first ≤ realDualHeight second ↔
      first.val 1 0 ^ 2 + first.val 1 1 ^ 2 ≤ second.val 1 0 ^ 2 + second.val 1 1 ^ 2 := by
  have det_positive : 0 < first.val.det ^ 2 := sq_pos_of_ne_zero first.det_ne_zero
  have corner_positive : 0 < first.val 2 2 ^ 2 := sq_pos_of_ne_zero (real_plane_corner_ne_zero first first_parabolic)
  have det_squares : first.val.det ^ 2 = second.val.det ^ 2 := by
    calc
      _ = |first.val.det| ^ 2 := (sq_abs _).symm
      _ = |second.val.det| ^ 2 := by rw [determinants]
      _ = _ := sq_abs _
  have first_formula := realDualHeight_projected_row_sq first first_parabolic
  have second_formula := realDualHeight_projected_row_sq second second_parabolic
  rw [← det_squares, ← corners] at second_formula
  rw [← sq_le_sq₀ (realDualHeight_pos first).le (realDualHeight_pos second).le]
  calc
    _ ↔ realDualHeight first ^ 2 * first.val.det ^ 2 ≤ realDualHeight second ^ 2 * first.val.det ^ 2 :=
      (mul_le_mul_iff_left₀ det_positive).symm
    _ ↔ _ := by rw [first_formula, second_formula, mul_le_mul_iff_right₀ corner_positive]

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
