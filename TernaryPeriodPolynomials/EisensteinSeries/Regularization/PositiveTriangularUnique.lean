module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Reduced.Orientation

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

def realPositiveTriangular (matrix : RealGL3) : Prop :=
  InPlaneParabolic matrix ∧ matrix.val 1 0 = 0 ∧
    0 < matrix.val 0 0 ∧ 0 < matrix.val 1 1 ∧ 0 < matrix.val 2 2

theorem realTriangularReduced_positiveTriangular {matrix : RealGL3}
    (reduced : realTriangularReduced matrix) (positive : 0 < matrix.val 0 0) :
    realPositiveTriangular matrix :=
  ⟨reduced.1, reduced.2.1, positive, reduced.2.2.1, reduced.2.2.2.1⟩

theorem realPositiveTriangular_gram_injective {first second : RealGL3}
    (first_triangular : realPositiveTriangular first)
    (second_triangular : realPositiveTriangular second)
    (gram : first.val * first.val.transpose = second.val * second.val.transpose) :
    first = second := by
  rcases first_triangular with ⟨⟨first20, first21⟩, first10, first00pos, first11pos, first22pos⟩
  rcases second_triangular with ⟨⟨second20, second21⟩, second10, second00pos, second11pos, second22pos⟩
  have entries (row column : Fin 3) := congrArg (fun matrix : Matrix (Fin 3) (Fin 3) ℝ => matrix row column) gram
  have last : first.val 2 2 = second.val 2 2 := by
    have h := entries 2 2
    simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply,
      first20, first21, second20, second21, zero_mul, zero_add] at h
    nlinarith
  have vertical1 : first.val 1 2 = second.val 1 2 := by
    have h := entries 1 2
    simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply,
      first20, first21, second20, second21, mul_zero, zero_add, last] at h
    exact mul_right_cancel₀ (ne_of_gt second22pos) h
  have vertical0 : first.val 0 2 = second.val 0 2 := by
    have h := entries 0 2
    simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply,
      first20, first21, second20, second21, mul_zero, zero_add, last] at h
    exact mul_right_cancel₀ (ne_of_gt second22pos) h
  have middle : first.val 1 1 = second.val 1 1 := by
    have h := entries 1 1
    simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply,
      first10, second10, zero_mul, zero_add, vertical1] at h
    nlinarith
  have horizontal : first.val 0 1 = second.val 0 1 := by
    have h := entries 0 1
    simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply,
      first10, second10, mul_zero, zero_add, vertical0, vertical1, middle] at h
    exact mul_right_cancel₀ (ne_of_gt second11pos) (add_right_cancel h)
  have initial : first.val 0 0 = second.val 0 0 := by
    have h := entries 0 0
    simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply,
      horizontal, vertical0] at h
    nlinarith
  apply Units.ext
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [first20, first21, first10, second20, second21, second10,
      initial, middle, last, horizontal, vertical0, vertical1]

theorem real_orthogonal_right_gram (matrix rotation : RealGL3)
    (orthogonal : rotation.val.transpose * rotation.val = 1) :
    (matrix * rotation).val * (matrix * rotation).val.transpose =
      matrix.val * matrix.val.transpose := by
  have inverse := real_orthogonal_inverse orthogonal
  change (matrix.val * rotation.val) * (matrix.val * rotation.val).transpose = _
  rw [Matrix.transpose_mul, ← inverse]
  simp only [mul_assoc, ← mul_assoc rotation.val rotation.inv, rotation.val_inv, one_mul]

theorem realPositiveTriangular_orthogonal_unique {first second firstRotation secondRotation : RealGL3}
    (first_triangular : realPositiveTriangular first)
    (second_triangular : realPositiveTriangular second)
    (first_orthogonal : firstRotation.val.transpose * firstRotation.val = 1)
    (second_orthogonal : secondRotation.val.transpose * secondRotation.val = 1)
    (equality : first * firstRotation = second * secondRotation) :
    first = second ∧ firstRotation = secondRotation := by
  have gram := congrArg (fun matrix : RealGL3 => matrix.val * matrix.val.transpose) equality
  rw [real_orthogonal_right_gram _ _ first_orthogonal,
    real_orthogonal_right_gram _ _ second_orthogonal] at gram
  have triangular_eq := realPositiveTriangular_gram_injective first_triangular second_triangular gram
  exact ⟨triangular_eq, mul_left_cancel (triangular_eq ▸ equality)⟩

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
