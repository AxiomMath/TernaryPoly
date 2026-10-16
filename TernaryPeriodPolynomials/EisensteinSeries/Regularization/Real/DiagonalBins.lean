module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.DiagonalRatioBounds

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

theorem realSpecialDiagonal_bin (diagonal : SpecialLinearGroup (Fin 3) ℝ)
    (positive : realPositiveDiagonal (SpecialLinearGroup.toGL diagonal))
    (lower01 : 1 / 2 ≤ diagonal.val 0 0 / diagonal.val 1 1)
    (lower12 : 1 / 2 ≤ diagonal.val 1 1 / diagonal.val 2 2) :
    ∃ m n : ℕ, realSpecialScaling (-(m : ℤ)) (-(n : ℤ)) * diagonal ∈ realSpecialDiagonalBox (1 / 64) 64 := by
  obtain ⟨m, m_bounds⟩ := real_ratio_power_bin lower01
  obtain ⟨n, n_bounds⟩ := real_ratio_power_bin lower12
  let scaling := realSpecialScaling (-(m : ℤ)) (-(n : ℤ))
  have scaling_positive := realSpecialScaling_positive (-(m : ℤ)) (-(n : ℤ))
  have product_positive : realPositiveDiagonal (SpecialLinearGroup.toGL (scaling * diagonal)) := by
    rw [map_mul]
    exact realPositiveDiagonal_mul scaling_positive positive
  have ratio01 : (scaling * diagonal).val 0 0 / (scaling * diagonal).val 1 1 =
      (diagonal.val 0 0 / diagonal.val 1 1) / (8 : ℝ) ^ m := by
    have identity := realPositiveDiagonal_mul_ratio scaling_positive positive 0 1
    rw [← map_mul] at identity
    change (scaling * diagonal).val 0 0 / (scaling * diagonal).val 1 1 =
      (scaling.val 0 0 / scaling.val 1 1) * (diagonal.val 0 0 / diagonal.val 1 1) at identity
    rw [identity, realSpecialScaling_ratio01, _root_.zpow_neg, zpow_natCast]
    ring
  have ratio12 : (scaling * diagonal).val 1 1 / (scaling * diagonal).val 2 2 =
      (diagonal.val 1 1 / diagonal.val 2 2) / (8 : ℝ) ^ n := by
    have identity := realPositiveDiagonal_mul_ratio scaling_positive positive 1 2
    rw [← map_mul] at identity
    change (scaling * diagonal).val 1 1 / (scaling * diagonal).val 2 2 =
      (scaling.val 1 1 / scaling.val 2 2) * (diagonal.val 1 1 / diagonal.val 2 2) at identity
    rw [identity, realSpecialScaling_ratio12, _root_.zpow_neg, zpow_natCast]
    ring
  refine ⟨m, n, realSpecialDiagonalBox_of_ratios product_positive ?_ ?_⟩
  · rwa [ratio01]
  · rwa [ratio12]

theorem realPositiveTriangular_diagonal_factor (matrix : SpecialLinearGroup (Fin 3) ℝ)
    (triangular : realPositiveTriangular (SpecialLinearGroup.toGL matrix)) :
    ∃ diagonal : SpecialLinearGroup (Fin 3) ℝ,
      realPositiveDiagonal (SpecialLinearGroup.toGL diagonal) ∧
      (∀ index, diagonal.val index index = matrix.val index index) ∧
      matrix = realSpecialUnipotent (matrix.val 0 1 / matrix.val 1 1)
        (matrix.val 1 2 / matrix.val 2 2) (matrix.val 0 2 / matrix.val 2 2) * diagonal := by
  rcases triangular with ⟨parabolic, triangular, pos0, pos1, pos2⟩
  have determinant : matrix.val 0 0 * matrix.val 1 1 * matrix.val 2 2 = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe matrix
    change (SpecialLinearGroup.toGL matrix).val.det = 1 at h
    rw [real_plane_determinant _ parabolic, triangular] at h
    simp only [mul_zero, sub_zero] at h
    exact h
  let diagonal : SpecialLinearGroup (Fin 3) ℝ :=
    ⟨!![matrix.val 0 0, 0, 0; 0, matrix.val 1 1, 0; 0, 0, matrix.val 2 2], by
      simpa [Matrix.det_fin_three] using determinant⟩
  have diagonal_positive : realPositiveDiagonal (SpecialLinearGroup.toGL diagonal) := by
    constructor
    · intro row column different
      fin_cases row <;> fin_cases column <;> simp_all [diagonal]
    · intro index
      fin_cases index
      · exact pos0
      · exact pos1
      · exact pos2
  refine ⟨diagonal, diagonal_positive, ?_, ?_⟩
  · intro index
    fin_cases index <;> rfl
  · apply Subtype.ext
    change matrix.val = (SpecialLinearGroup.toGL (realSpecialUnipotent _ _ _ * diagonal)).val
    rw [realSpecialUnipotent_diagonal_val _ _ _ _ diagonal_positive]
    have nonzero1 : matrix.val 1 1 ≠ 0 := ne_of_gt pos1
    have nonzero2 : matrix.val 2 2 ≠ 0 := ne_of_gt pos2
    have zero10 : matrix.val 1 0 = 0 := triangular
    have zero20 : matrix.val 2 0 = 0 := parabolic.1
    have zero21 : matrix.val 2 1 = 0 := parabolic.2
    ext row column
    fin_cases row <;> fin_cases column <;>
      simp [diagonal, div_mul_cancel₀ _ nonzero1, div_mul_cancel₀ _ nonzero2, zero10, zero20, zero21]

theorem realTriangularReduced_diagonal_ratios {matrix : RealGL3}
    (reduced : realTriangularReduced matrix) (positive : 0 < matrix.val 0 0) :
    1 / 2 ≤ matrix.val 0 0 / matrix.val 1 1 ∧ 1 / 2 ≤ matrix.val 1 1 / matrix.val 2 2 := by
  rcases reduced with ⟨_, _, pos1, pos2, _, _, _, bound01, bound12⟩
  constructor
  · apply (le_div_iff₀ pos1).mpr
    by_contra! small
    have difference : 0 < matrix.val 1 1 - 2 * matrix.val 0 0 := by linarith
    have sum : 0 < matrix.val 1 1 + 2 * matrix.val 0 0 := by positivity
    nlinarith [mul_pos difference sum]
  · apply (le_div_iff₀ pos2).mpr
    by_contra! small
    have difference : 0 < matrix.val 2 2 - 2 * matrix.val 1 1 := by linarith
    have sum : 0 < matrix.val 2 2 + 2 * matrix.val 1 1 := by positivity
    nlinarith [mul_pos difference sum]

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
