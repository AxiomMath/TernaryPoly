module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Special.LinearBoxVolume
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section


open Matrix MeasureTheory
open scoped Pointwise ENNReal

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem realSpecialShrinkingBox_translate_union_finite
    (shift : ℕ → ℕ → SpecialLinearGroup (Fin 3) ℝ)
    {diagonals : Set (SpecialLinearGroup (Fin 3) ℝ)} (compact : IsCompact diagonals)
    (positive : ∀ diagonal ∈ diagonals, realPositiveDiagonal (SpecialLinearGroup.toGL diagonal)) :
    realSpecialLinearHaar (⋃ m, ⋃ n, shift m n • realSpecialShrinkingBox m n diagonals) < ⊤ := by
  let bound := realSpecialLinearHaar (realSpecialSiegelBox 4 4 4 diagonals)
  have bound_finite : bound < ⊤ := (realSpecialSiegelBox_isCompact 4 4 4 compact).measure_lt_top
  have majorant : (∑' m : ℕ, ∑' n : ℕ, (64 : ℝ≥0∞)⁻¹ ^ (m + n) * bound) < ⊤ := by
    simp only [pow_add, mul_assoc, ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, ENNReal.tsum_geometric]
    have geometric_finite : (1 - (64 : ℝ≥0∞)⁻¹)⁻¹ ≠ ⊤ :=
      ENNReal.inv_ne_top.mpr (ne_of_gt (tsub_pos_iff_lt.mpr (ENNReal.inv_lt_one.mpr (by norm_num))))
    exact ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr geometric_finite)
      (ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr geometric_finite) bound_finite)
  apply lt_of_le_of_lt _ majorant
  calc
    _ ≤ ∑' m : ℕ, realSpecialLinearHaar (⋃ n, shift m n • realSpecialShrinkingBox m n diagonals) :=
      measure_iUnion_le _
    _ ≤ ∑' m : ℕ, ∑' n : ℕ, realSpecialLinearHaar (shift m n • realSpecialShrinkingBox m n diagonals) :=
      ENNReal.tsum_le_tsum (fun _ => measure_iUnion_le _)
    _ ≤ ∑' m : ℕ, ∑' n : ℕ, (64 : ℝ≥0∞)⁻¹ ^ (m + n) * bound := by
      apply ENNReal.tsum_le_tsum
      intro m
      apply ENNReal.tsum_le_tsum
      intro n
      rw [measure_smul]
      exact realSpecialShrinkingBox_volume_bound m n compact positive

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
