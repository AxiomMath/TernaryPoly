module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.ScalingRowBounds
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Reduced.ShrinkingCover

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Pointwise

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

theorem realSpecialShrinkingBox_subset_fixed (m n : ℕ) (diagonals : Set (SpecialLinearGroup (Fin 3) ℝ)) :
    realSpecialShrinkingBox m n diagonals ⊆ realSpecialSiegelBox (1 / 2) (1 / 2) (1 / 2) diagonals := by
  intro matrix member
  obtain ⟨x, y, z, diagonal, rotation, hx, hy, hz, hd, hk, equality⟩ := mem_realSpecialSiegelBox_iff.mp member
  exact mem_realSpecialSiegelBox_iff.mpr ⟨x, y, z, diagonal, rotation,
    hx.trans (realSpecialBoxRadius_le_half m), hy.trans (realSpecialBoxRadius_le_half n),
    hz.trans (realSpecialBoxRadius_le_half (m + n)), hd, hk, equality⟩

theorem real_scaled_compact_row_bound (matrices : Set (SpecialLinearGroup (Fin 3) ℝ)) (compact : IsCompact matrices) :
    ∃ bound : ℝ, 1 ≤ bound ∧ ∀ m n : ℕ, ∀ matrix ∈ matrices, ∀ row : Fin 3 → ℝ,
      ‖row‖ ≤ ((2 : ℝ) ^ (m + 2 * n) * bound) *
        ‖row ᵥ* (SpecialLinearGroup.toGL (realSpecialScaling m n * matrix)).val‖ := by
  obtain ⟨bound, _, bounded⟩ := real_compact_inverse_row_bound
    (SpecialLinearGroup.toGL '' matrices) (compact.image SpecialLinearGroup.continuous_toGL)
  refine ⟨max 1 bound, le_max_left _ _, ?_⟩
  intro m n matrix member row
  have compact_bound := bounded _ ⟨matrix, member, rfl⟩
    (row ᵥ* (SpecialLinearGroup.toGL (realSpecialScaling m n)).val)
  calc
    ‖row‖ ≤ (2 : ℝ) ^ (m + 2 * n) * ‖row ᵥ* (SpecialLinearGroup.toGL (realSpecialScaling m n)).val‖ :=
      realSpecialScaling_row_bound m n row
    _ ≤ (2 : ℝ) ^ (m + 2 * n) * (max 1 bound *
        ‖(row ᵥ* (SpecialLinearGroup.toGL (realSpecialScaling m n)).val) ᵥ*
          (SpecialLinearGroup.toGL matrix).val‖) :=
      mul_le_mul_of_nonneg_left (compact_bound.trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))) (by positivity)
    _ = _ := by
      rw [Matrix.vecMul_vecMul, map_mul]
      exact (mul_assoc _ _ _).symm

theorem realSpecialShrinkingTranslate_row_bound
    {diagonals : Set (SpecialLinearGroup (Fin 3) ℝ)} (compact : IsCompact diagonals) :
    ∃ bound : ℝ, 1 ≤ bound ∧ ∀ m n : ℕ,
      ∀ matrix ∈ realSpecialScaling m n • realSpecialShrinkingBox m n diagonals, ∀ row : Fin 3 → ℝ,
        ‖row‖ ≤ ((2 : ℝ) ^ (m + 2 * n) * bound) * ‖row ᵥ* (SpecialLinearGroup.toGL matrix).val‖ := by
  obtain ⟨bound, large, bounded⟩ := real_scaled_compact_row_bound _
    (realSpecialSiegelBox_isCompact (1 / 2) (1 / 2) (1 / 2) compact)
  refine ⟨bound, large, ?_⟩
  intro m n matrix member row
  obtain ⟨factor, factor_member, rfl⟩ := member
  exact bounded m n factor (realSpecialShrinkingBox_subset_fixed m n diagonals factor_member) row

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
