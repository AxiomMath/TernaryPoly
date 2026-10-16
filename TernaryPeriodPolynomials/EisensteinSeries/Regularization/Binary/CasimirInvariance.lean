module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Cusp.RankOneOperators

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped BigOperators

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem binary_conjugate_single_expansion (matrix : BinaryRealGL) (i j : Fin 2) :
    matrix.inv * Matrix.single i j (1 : ℝ) * matrix.val =
      ∑ index : Fin 2 × Fin 2,
        (matrix.inv index.1 i * matrix.val j index.2) • Matrix.single index.1 index.2 (1 : ℝ) := by
  rw [Fintype.sum_prod_type]
  apply Matrix.ext
  intro row column
  fin_cases i <;> fin_cases j <;> fin_cases row <;> fin_cases column <;>
    simp [Fin.sum_univ_two, Matrix.mul_apply, Matrix.single_apply]

theorem binary_conjugation_contraction (matrix : BinaryRealGL) (first second : Fin 2 × Fin 2) :
    (∑ index : Fin 2 × Fin 2,
      (matrix.inv first.1 index.1 * matrix.val index.2 first.2) *
        (matrix.inv second.1 index.2 * matrix.val index.1 second.2)) =
      if second = (first.2, first.1) then 1 else 0 := by
  calc
    _ = ∑ i : Fin 2, ∑ j : Fin 2,
        (matrix.inv first.1 i * matrix.val i second.2) *
          (matrix.inv second.1 j * matrix.val j first.2) := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = (matrix.inv * matrix.val) first.1 second.2 *
        (matrix.inv * matrix.val) second.1 first.2 := by
      simp only [Matrix.mul_apply, Finset.sum_mul_sum]
    _ = _ := by
      rw [matrix.inv_val]
      rcases first with ⟨a, b⟩
      rcases second with ⟨c, d⟩
      fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> norm_num

theorem binary_quadratic_contraction_invariant {V : Type*} [AddCommGroup V] [Module ℂ V]
    (operator : Matrix (Fin 2) (Fin 2) ℝ →ₗ[ℝ] Module.End ℂ V) (matrix : BinaryRealGL) :
    (∑ index : Fin 2 × Fin 2,
      operator (matrix.inv * Matrix.single index.1 index.2 1 * matrix.val) *
        operator (matrix.inv * Matrix.single index.2 index.1 1 * matrix.val)) =
      ∑ index : Fin 2 × Fin 2,
        operator (Matrix.single index.1 index.2 1) * operator (Matrix.single index.2 index.1 1) := by
  simp_rw [binary_conjugate_single_expansion, map_sum, map_smul, Finset.sum_mul,
    Finset.mul_sum, smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [Finset.sum_comm_cycle, Finset.sum_comm_cycle]
  simp_rw [← Finset.sum_smul, binary_conjugation_contraction]
  simp

theorem binary_casimir_eq_contraction {V : Type*} [AddCommGroup V] [Module ℂ V]
    (operator : Matrix (Fin 2) (Fin 2) ℝ →ₗ[ℝ] Module.End ℂ V) :
    operator binarySplitDirection * operator binarySplitDirection +
      operator binarySymmetricDirection * operator binarySymmetricDirection -
        operator binaryRotationDirection * operator binaryRotationDirection =
      2 • (∑ index : Fin 2 × Fin 2,
        operator (Matrix.single index.1 index.2 1) * operator (Matrix.single index.2 index.1 1)) -
          operator 1 * operator 1 := by
  have split : binarySplitDirection = Matrix.single 0 0 (1 : ℝ) - Matrix.single 1 1 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [binarySplitDirection, Matrix.single_apply]
  have symmetric : binarySymmetricDirection = Matrix.single 0 1 (1 : ℝ) + Matrix.single 1 0 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [binarySymmetricDirection, Matrix.single_apply]
  have rotation : binaryRotationDirection = Matrix.single 0 1 (1 : ℝ) - Matrix.single 1 0 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [binaryRotationDirection, Matrix.single_apply]
  have identity : (1 : Matrix (Fin 2) (Fin 2) ℝ) = Matrix.single 0 0 1 + Matrix.single 1 1 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.single_apply]
  rw [split, symmetric, rotation, identity]
  simp only [map_add, map_sub, Fintype.sum_prod_type, Fin.sum_univ_two, two_smul]
  noncomm_ring

theorem binary_casimir_conjugation_invariant {V : Type*} [AddCommGroup V] [Module ℂ V]
    (operator : Matrix (Fin 2) (Fin 2) ℝ →ₗ[ℝ] Module.End ℂ V) (matrix : BinaryRealGL) :
    operator (matrix.inv * binarySplitDirection * matrix.val) *
        operator (matrix.inv * binarySplitDirection * matrix.val) +
      operator (matrix.inv * binarySymmetricDirection * matrix.val) *
        operator (matrix.inv * binarySymmetricDirection * matrix.val) -
      operator (matrix.inv * binaryRotationDirection * matrix.val) *
        operator (matrix.inv * binaryRotationDirection * matrix.val) =
    operator binarySplitDirection * operator binarySplitDirection +
      operator binarySymmetricDirection * operator binarySymmetricDirection -
        operator binaryRotationDirection * operator binaryRotationDirection := by
  let conjugation : Matrix (Fin 2) (Fin 2) ℝ →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℝ :=
    (LinearMap.mulRight ℝ matrix.val).comp (LinearMap.mulLeft ℝ matrix.inv)
  have equality := binary_casimir_eq_contraction (operator.comp conjugation)
  change _ = 2 • (∑ index : Fin 2 × Fin 2,
      operator (matrix.inv * Matrix.single index.1 index.2 1 * matrix.val) *
        operator (matrix.inv * Matrix.single index.2 index.1 1 * matrix.val)) -
      operator (matrix.inv * 1 * matrix.val) * operator (matrix.inv * 1 * matrix.val) at equality
  rw [binary_quadratic_contraction_invariant, mul_one, matrix.inv_val,
    ← binary_casimir_eq_contraction] at equality
  exact equality

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
