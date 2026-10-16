module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Special.LinearMatrixBounds
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Residue.GroupAverages
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Reduced.PieceRowBounds

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Matrix.Norms.Elementwise Pointwise

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

theorem realSpecialPlane_inverse (first second : ℝ) :
    (realSpecialPlane first second)⁻¹ = realSpecialPlane (-first) (-second) := by
  apply inv_eq_of_mul_eq_one_right
  rw [realSpecialPlane, realSpecialPlane, realSpecialUnipotent_mul]
  simp only [add_neg_cancel, zero_add, zero_mul]
  apply Subtype.ext
  ext row column
  fin_cases row <;> fin_cases column <;> norm_num [realSpecialUnipotent]

theorem realSpecialPlane_norm_sub_one_le {bound first second : ℝ} (nonnegative : 0 ≤ bound)
    (first_bound : |first| ≤ bound) (second_bound : |second| ≤ bound) :
    ‖(realSpecialPlane first second).val - 1‖ ≤ bound := by
  apply (Matrix.norm_le_iff nonnegative).mpr
  intro row column
  fin_cases row <;> fin_cases column <;>
    simpa [realSpecialPlane, realSpecialUnipotent, Real.norm_eq_abs] using
      (by first | exact first_bound | exact second_bound | exact nonnegative)

theorem realSpecialScaling_plane_conjugation (m n : ℕ) (first second : ℝ) :
    (realSpecialScaling m n)⁻¹ * realSpecialPlane first second * realSpecialScaling m n =
      realSpecialPlane ((8 : ℝ)⁻¹ ^ (m + n) * first) ((8 : ℝ)⁻¹ ^ n * second) := by
  rw [realSpecialScaling_inv, realSpecialPlane, realSpecialScaling_negative_unipotent, mul_assoc,
    ← realSpecialScaling_inv, inv_mul_cancel, mul_one, mul_zero]
  rfl

theorem realSpecialScaling_plane_contraction (m n : ℕ) {first second : ℝ}
    (first_bound : |first| ≤ 3) (second_bound : |second| ≤ 3) :
    ‖((realSpecialScaling m n)⁻¹ * realSpecialPlane first second * realSpecialScaling m n).val - 1‖ ≤
      3 * (8 : ℝ)⁻¹ ^ n := by
  rw [realSpecialScaling_plane_conjugation]
  apply realSpecialPlane_norm_sub_one_le (by positivity)
  · rw [abs_mul, abs_of_pos (by positivity : 0 < (8 : ℝ)⁻¹ ^ (m + n)), pow_add]
    calc
      _ ≤ ((8 : ℝ)⁻¹ ^ m * (8 : ℝ)⁻¹ ^ n) * 3 := mul_le_mul_of_nonneg_left first_bound (by positivity)
      _ ≤ (1 * (8 : ℝ)⁻¹ ^ n) * 3 := by
        gcongr
        exact pow_le_one₀ (by norm_num) (by norm_num)
      _ = _ := by ring
  · rw [abs_mul, abs_of_pos (by positivity : 0 < (8 : ℝ)⁻¹ ^ n)]
    exact (mul_le_mul_of_nonneg_left second_bound (by positivity)).trans_eq (mul_comm _ _)

theorem real_scaled_compact_plane_contraction
    {matrices : Set (SpecialLinearGroup (Fin 3) ℝ)} (compact : IsCompact matrices) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ m n : ℕ, ∀ matrix ∈ matrices, ∀ first second : ℝ,
      |first| ≤ 3 → |second| ≤ 3 →
      ‖((realSpecialScaling m n * matrix)⁻¹ * realSpecialPlane first second *
        (realSpecialScaling m n * matrix)).val - 1‖ ≤ bound * (8 : ℝ)⁻¹ ^ n := by
  obtain ⟨bound, nonnegative, bounded⟩ := realSpecialLinear_compact_conjugation_bound compact
  refine ⟨bound * 3, by positivity, ?_⟩
  intro m n matrix member first second first_bound second_bound
  have identity : (realSpecialScaling m n * matrix)⁻¹ * realSpecialPlane first second *
      (realSpecialScaling m n * matrix) = matrix⁻¹ *
        ((realSpecialScaling m n)⁻¹ * realSpecialPlane first second * realSpecialScaling m n) * matrix := by group
  rw [identity]
  exact (bounded matrix member _).trans
    ((mul_le_mul_of_nonneg_left (realSpecialScaling_plane_contraction m n first_bound second_bound)
      nonnegative).trans_eq (mul_assoc _ _ _).symm)

theorem realSpecialShrinkingTranslate_plane_contraction
    {diagonals : Set (SpecialLinearGroup (Fin 3) ℝ)} (compact : IsCompact diagonals) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ m n : ℕ,
      ∀ matrix ∈ realSpecialScaling m n • realSpecialShrinkingBox m n diagonals,
      ∀ first second : ℝ, |first| ≤ 3 → |second| ≤ 3 →
      ‖(matrix⁻¹ * realSpecialPlane first second * matrix).val - 1‖ ≤ bound * (8 : ℝ)⁻¹ ^ n := by
  obtain ⟨bound, nonnegative, bounded⟩ := real_scaled_compact_plane_contraction
    (realSpecialSiegelBox_isCompact (1 / 2) (1 / 2) (1 / 2) compact)
  refine ⟨bound, nonnegative, ?_⟩
  intro m n matrix member first second first_bound second_bound
  obtain ⟨factor, factor_member, rfl⟩ := member
  exact bounded m n factor (realSpecialShrinkingBox_subset_fixed m n diagonals factor_member)
    first second first_bound second_bound

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
