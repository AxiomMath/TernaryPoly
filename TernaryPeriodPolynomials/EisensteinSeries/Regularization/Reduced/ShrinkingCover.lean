module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Real.DiagonalBins
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.ShrinkingCoverVolume

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open scoped Pointwise ENNReal

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

theorem realSpecialScaling_negative_unipotent (m n : ℕ) (x y z : ℝ) :
    realSpecialScaling (-(m : ℤ)) (-(n : ℤ)) * realSpecialUnipotent x y z =
      realSpecialUnipotent ((8 : ℝ)⁻¹ ^ m * x) ((8 : ℝ)⁻¹ ^ n * y) ((8 : ℝ)⁻¹ ^ (m + n) * z) *
        realSpecialScaling (-(m : ℤ)) (-(n : ℤ)) := by
  have exponents : -(m : ℤ) + -(n : ℤ) = -((m + n : ℕ) : ℤ) := by push_cast; ring
  simpa only [exponents, _root_.zpow_neg, zpow_natCast, inv_pow] using
    realSpecialScaling_unipotent (-(m : ℤ)) (-(n : ℤ)) x y z

theorem realSpecialBoxRadius_scaled_bound {value : ℝ} (bound : |value| ≤ 1 / 2) (index : ℕ) :
    |(8 : ℝ)⁻¹ ^ index * value| ≤ realSpecialBoxRadius index := by
  rw [abs_mul, abs_of_pos (by positivity : 0 < (8 : ℝ)⁻¹ ^ index)]
  exact (mul_le_mul_of_nonneg_left bound (by positivity)).trans_eq (by unfold realSpecialBoxRadius; ring)

theorem realSpecialShrinkingBox_scaled_member (m n : ℕ) {x y z : ℝ}
    (hx : |x| ≤ 1 / 2) (hy : |y| ≤ 1 / 2) (hz : |z| ≤ 1 / 2)
    {diagonal rotation : SpecialLinearGroup (Fin 3) ℝ}
    (diagonal_bin : realSpecialScaling (-(m : ℤ)) (-(n : ℤ)) * diagonal ∈ realSpecialDiagonalBox (1 / 64) 64)
    (orthogonal : rotation ∈ realSpecialOrthogonal) :
    realSpecialScaling (-(m : ℤ)) (-(n : ℤ)) * (realSpecialUnipotent x y z * diagonal * rotation) ∈
      realSpecialShrinkingBox m n (realSpecialDiagonalBox (1 / 64) 64) := by
  apply mem_realSpecialSiegelBox_iff.mpr
  refine ⟨(8 : ℝ)⁻¹ ^ m * x, (8 : ℝ)⁻¹ ^ n * y, (8 : ℝ)⁻¹ ^ (m + n) * z,
    realSpecialScaling (-(m : ℤ)) (-(n : ℤ)) * diagonal, rotation,
    realSpecialBoxRadius_scaled_bound hx m, realSpecialBoxRadius_scaled_bound hy n,
    realSpecialBoxRadius_scaled_bound hz (m + n), diagonal_bin, orthogonal, ?_⟩
  simp only [← mul_assoc, realSpecialScaling_negative_unipotent]

theorem realSpecialLinearReducedCover_subset_shrinking :
    realSpecialLinearReducedCover ⊆
      ⋃ m : ℕ, ⋃ n : ℕ, realSpecialScaling m n •
        realSpecialShrinkingBox m n (realSpecialDiagonalBox (1 / 64) 64) := by
  rintro matrix ⟨triangular, rotation, reduced, positive, orthogonal, rfl⟩
  obtain ⟨diagonal, diagonal_positive, diagonals, factor⟩ :=
    realPositiveTriangular_diagonal_factor triangular (realTriangularReduced_positiveTriangular reduced positive)
  obtain ⟨lower01, lower12⟩ := realTriangularReduced_diagonal_ratios reduced positive
  have diagonal_lower01 : 1 / 2 ≤ diagonal.val 0 0 / diagonal.val 1 1 := by
    rw [diagonals, diagonals]
    exact lower01
  have diagonal_lower12 : 1 / 2 ≤ diagonal.val 1 1 / diagonal.val 2 2 := by
    rw [diagonals, diagonals]
    exact lower12
  obtain ⟨m, n, diagonal_bin⟩ := realSpecialDiagonal_bin diagonal diagonal_positive diagonal_lower01 diagonal_lower12
  have hx : |triangular.val 0 1 / triangular.val 1 1| ≤ 1 / 2 := by
    change |(SpecialLinearGroup.toGL triangular).val 0 1 / (SpecialLinearGroup.toGL triangular).val 1 1| ≤ 1 / 2
    rw [abs_div, abs_of_pos reduced.2.2.1]
    apply (div_le_iff₀ reduced.2.2.1).mpr
    exact reduced.2.2.2.2.1.trans_eq (by ring)
  have hy : |triangular.val 1 2 / triangular.val 2 2| ≤ 1 / 2 := by
    change |(SpecialLinearGroup.toGL triangular).val 1 2 / (SpecialLinearGroup.toGL triangular).val 2 2| ≤ 1 / 2
    rw [abs_div, abs_of_pos reduced.2.2.2.1]
    apply (div_le_iff₀ reduced.2.2.2.1).mpr
    exact reduced.2.2.2.2.2.2.1.trans_eq (by ring)
  have hz : |triangular.val 0 2 / triangular.val 2 2| ≤ 1 / 2 := by
    change |(SpecialLinearGroup.toGL triangular).val 0 2 / (SpecialLinearGroup.toGL triangular).val 2 2| ≤ 1 / 2
    rw [abs_div, abs_of_pos reduced.2.2.2.1]
    apply (div_le_iff₀ reduced.2.2.2.1).mpr
    exact reduced.2.2.2.2.2.1.trans_eq (by ring)
  have member : realSpecialScaling (-(m : ℤ)) (-(n : ℤ)) * (triangular * rotation) ∈
      realSpecialShrinkingBox m n (realSpecialDiagonalBox (1 / 64) 64) := by
    rw [factor]
    exact realSpecialShrinkingBox_scaled_member m n hx hy hz diagonal_bin orthogonal
  apply Set.mem_iUnion.mpr
  refine ⟨m, Set.mem_iUnion.mpr ⟨n, ?_⟩⟩
  refine ⟨_, member, ?_⟩
  change realSpecialScaling m n * (realSpecialScaling (-(m : ℤ)) (-(n : ℤ)) * (triangular * rotation)) = _
  rw [← realSpecialScaling_inv, mul_inv_cancel_left]

theorem realSpecialLinearReducedCover_measure_finite :
    realSpecialLinearHaar realSpecialLinearReducedCover < ⊤ := by
  apply lt_of_le_of_lt (measure_mono realSpecialLinearReducedCover_subset_shrinking)
  exact realSpecialShrinkingBox_translate_union_finite
    (fun m n => realSpecialScaling m n) (realSpecialDiagonalBox_isCompact (1 / 64) 64)
    (fun _ member => realSpecialDiagonalBox_positive (by norm_num) member)

theorem integerSpecialLinearQuotientMeasure_finite : integerSpecialLinearQuotientMeasure Set.univ < ⊤ :=
  lt_of_le_of_lt integerSpecialLinearQuotientMeasure_le_reducedCover realSpecialLinearReducedCover_measure_finite

instance integerSpecialLinearQuotientMeasure_isFinite : IsFiniteMeasure integerSpecialLinearQuotientMeasure :=
  ⟨integerSpecialLinearQuotientMeasure_finite⟩

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
