module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Special.LinearDomain
public import Mathlib.Analysis.Matrix.Normed

@[expose] public section


open Matrix
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

theorem ternary_matrix_norm_mul_le (first second : Matrix (Fin 3) (Fin 3) ℝ) :
    ‖first * second‖ ≤ 3 * ‖first‖ * ‖second‖ := by
  apply (Matrix.norm_le_iff (by positivity)).mpr
  intro row column
  calc
    ‖(first * second) row column‖ ≤ ∑ index : Fin 3, ‖first row index * second index column‖ :=
      by simpa only [Matrix.mul_apply] using norm_sum_le Finset.univ (fun index => first row index * second index column)
    _ ≤ ∑ _index : Fin 3, ‖first‖ * ‖second‖ := by
      apply Finset.sum_le_sum
      intro index _
      rw [norm_mul]
      exact mul_le_mul (Matrix.norm_entry_le_entrywise_sup_norm first)
        (Matrix.norm_entry_le_entrywise_sup_norm second) (norm_nonneg _) (norm_nonneg _)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

theorem realSpecialLinear_compact_matrix_bounds
    {matrices : Set (SpecialLinearGroup (Fin 3) ℝ)} (compact : IsCompact matrices) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ matrix ∈ matrices, ‖matrix.val‖ ≤ bound ∧ ‖(matrix⁻¹).val‖ ≤ bound := by
  obtain ⟨first, first_bound⟩ := compact.exists_bound_of_continuousOn
    (show Continuous (fun matrix : SpecialLinearGroup (Fin 3) ℝ => matrix.val) from continuous_subtype_val).continuousOn
  obtain ⟨second, second_bound⟩ := compact.exists_bound_of_continuousOn
    (show Continuous (fun matrix : SpecialLinearGroup (Fin 3) ℝ => (matrix⁻¹).val) from
      continuous_subtype_val.comp continuous_inv).continuousOn
  refine ⟨max 0 (max first second), le_max_left _ _, ?_⟩
  intro matrix member
  exact ⟨(first_bound matrix member).trans ((le_max_left _ _).trans (le_max_right _ _)),
    (second_bound matrix member).trans ((le_max_right _ _).trans (le_max_right _ _))⟩

theorem realSpecialLinear_compact_conjugation_bound
    {matrices : Set (SpecialLinearGroup (Fin 3) ℝ)} (compact : IsCompact matrices) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ matrix ∈ matrices, ∀ argument : SpecialLinearGroup (Fin 3) ℝ,
      ‖(matrix⁻¹ * argument * matrix).val - 1‖ ≤ bound * ‖argument.val - 1‖ := by
  obtain ⟨bound, nonnegative, bounded⟩ := realSpecialLinear_compact_matrix_bounds compact
  refine ⟨9 * bound * bound, by positivity, ?_⟩
  intro matrix member argument
  have identity : (matrix⁻¹ * argument * matrix).val - 1 =
      (matrix⁻¹).val * (argument.val - 1) * matrix.val := by
    simp only [SpecialLinearGroup.coe_mul, mul_sub, sub_mul, mul_one]
    rw [show (matrix⁻¹).val * matrix.val = 1 from congrArg Subtype.val (inv_mul_cancel matrix)]
  rw [identity]
  calc
    _ ≤ 3 * ‖(matrix⁻¹).val * (argument.val - 1)‖ * ‖matrix.val‖ := ternary_matrix_norm_mul_le _ _
    _ ≤ 3 * (3 * ‖(matrix⁻¹).val‖ * ‖argument.val - 1‖) * ‖matrix.val‖ := by
      gcongr
      exact ternary_matrix_norm_mul_le _ _
    _ ≤ 3 * (3 * bound * ‖argument.val - 1‖) * bound := by
      gcongr
      · exact (bounded matrix member).2
      · exact (bounded matrix member).1
    _ = _ := by ring

theorem realSpecialLinear_norm_ball_compact (center : Matrix (Fin 3) (Fin 3) ℝ) (radius : ℝ) :
    IsCompact {matrix : SpecialLinearGroup (Fin 3) ℝ | ‖matrix.val - center‖ ≤ radius} := by
  have closed : Topology.IsClosedEmbedding
      (fun matrix : SpecialLinearGroup (Fin 3) ℝ => matrix.val) := SpecialLinearGroup.isClosedEmbedding_val
  convert closed.isCompact_preimage (isCompact_closedBall center radius) using 1
  ext matrix
  simp only [Set.mem_ofPred_eq, Set.mem_preimage, Metric.mem_closedBall]
  rfl

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
