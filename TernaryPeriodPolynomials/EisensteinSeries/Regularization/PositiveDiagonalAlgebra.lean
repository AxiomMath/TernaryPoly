module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Real.DiagonalScaling

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

theorem realPositiveDiagonal_val {matrix : RealGL3} (diagonal : realPositiveDiagonal matrix) :
    matrix.val = Matrix.diagonal (fun index => matrix.val index index) := by
  ext row column
  by_cases equal : row = column
  · subst column
    simp
  · simp [equal, diagonal.1 row column equal]

theorem realPositiveDiagonal_mul_val {first second : RealGL3}
    (first_diagonal : realPositiveDiagonal first) (second_diagonal : realPositiveDiagonal second) :
    (first * second).val = Matrix.diagonal (fun index => first.val index index * second.val index index) := by
  change first.val * second.val = _
  conv_lhs => rw [realPositiveDiagonal_val first_diagonal, realPositiveDiagonal_val second_diagonal]
  exact Matrix.diagonal_mul_diagonal _ _

theorem realPositiveDiagonal_mul {first second : RealGL3}
    (first_diagonal : realPositiveDiagonal first) (second_diagonal : realPositiveDiagonal second) :
    realPositiveDiagonal (first * second) := by
  constructor
  · intro row column different
    rw [realPositiveDiagonal_mul_val first_diagonal second_diagonal]
    exact Matrix.diagonal_apply_ne _ different
  · intro index
    rw [realPositiveDiagonal_mul_val first_diagonal second_diagonal, Matrix.diagonal_apply_eq]
    exact mul_pos (first_diagonal.2 index) (second_diagonal.2 index)

theorem realSpecialDiagonal_unipotent (diagonal : SpecialLinearGroup (Fin 3) ℝ)
    (diagonal_spec : realPositiveDiagonal (SpecialLinearGroup.toGL diagonal)) (x y z : ℝ) :
    diagonal * realSpecialUnipotent x y z =
      realSpecialUnipotent (diagonal.val 0 0 / diagonal.val 1 1 * x)
        (diagonal.val 1 1 / diagonal.val 2 2 * y) (diagonal.val 0 0 / diagonal.val 2 2 * z) * diagonal := by
  have off (row column : Fin 3) (different : row ≠ column) : diagonal.val row column = 0 :=
    diagonal_spec.1 row column different
  have middle : diagonal.val 1 1 ≠ 0 := ne_of_gt (diagonal_spec.2 1)
  have last : diagonal.val 2 2 ≠ 0 := ne_of_gt (diagonal_spec.2 2)
  apply Subtype.ext
  change diagonal.val * (realSpecialUnipotent x y z).val =
    (SpecialLinearGroup.toGL (realSpecialUnipotent _ _ _ * diagonal)).val
  rw [realSpecialUnipotent_diagonal_val _ _ _ _ diagonal_spec]
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [realSpecialUnipotent, Matrix.mul_apply, Fin.sum_univ_three,
      off 0 1 (by decide), off 0 2 (by decide), off 1 0 (by decide),
      off 1 2 (by decide), off 2 0 (by decide), off 2 1 (by decide)] <;>
    field_simp

theorem realSpecialScaling_unipotent (m n : ℤ) (x y z : ℝ) :
    realSpecialScaling m n * realSpecialUnipotent x y z =
      realSpecialUnipotent ((8 : ℝ) ^ m * x) ((8 : ℝ) ^ n * y) ((8 : ℝ) ^ (m + n) * z) *
        realSpecialScaling m n := by
  simpa only [realSpecialScaling_ratio01, realSpecialScaling_ratio12, realSpecialScaling_ratio02] using
    realSpecialDiagonal_unipotent (realSpecialScaling m n) (realSpecialScaling_positive m n) x y z

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
