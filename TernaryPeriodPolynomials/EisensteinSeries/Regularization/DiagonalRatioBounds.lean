module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.PositiveDiagonalAlgebra

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

theorem positive_product_coordinate_bounds {a b c : ℝ}
    (apos : 0 < a) (bpos : 0 < b) (product : a * b * c = 1)
    (ab : a ≤ 64 * b) (ac : a ≤ 64 * c) (ba : b ≤ 64 * a) (ca : c ≤ 64 * a) :
    a ∈ Set.Icc (1 / 64 : ℝ) 64 := by
  constructor
  · by_contra! small
    have aone : a < 1 := by linarith
    have bone : b < 1 := by linarith
    have cone : c < 1 := by linarith
    have ablt : a * b < 1 := ((mul_lt_mul_of_pos_left bone apos).trans_eq (mul_one a)).trans aone
    have abclt : a * b * c < a * b := by
      simpa only [mul_one] using mul_lt_mul_of_pos_left cone (mul_pos apos bpos)
    linarith
  · by_contra! large
    have aone : 1 < a := by linarith
    have bone : 1 < b := by linarith
    have cone : 1 < c := by linarith
    have abgt : 1 < a * b := one_lt_mul aone.le bone
    have abcgt : 1 < a * b * c := one_lt_mul abgt.le cone
    linarith

theorem positive_triple_ratio_bounds {a b c : ℝ}
    (apos : 0 < a) (bpos : 0 < b) (cpos : 0 < c) (product : a * b * c = 1)
    (ratio01 : 1 / 2 ≤ a / b ∧ a / b ≤ 8) (ratio12 : 1 / 2 ≤ b / c ∧ b / c ≤ 8) :
    a ∈ Set.Icc (1 / 64 : ℝ) 64 ∧ b ∈ Set.Icc (1 / 64 : ℝ) 64 ∧ c ∈ Set.Icc (1 / 64 : ℝ) 64 := by
  have lower01 := (le_div_iff₀ bpos).mp ratio01.1
  have upper01 := (div_le_iff₀ bpos).mp ratio01.2
  have lower12 := (le_div_iff₀ cpos).mp ratio12.1
  have upper12 := (div_le_iff₀ cpos).mp ratio12.2
  have ab : a ≤ 64 * b := by linarith
  have ac : a ≤ 64 * c := by linarith
  have ba : b ≤ 64 * a := by linarith
  have bc : b ≤ 64 * c := by linarith
  have ca : c ≤ 64 * a := by linarith
  have cb : c ≤ 64 * b := by linarith
  refine ⟨positive_product_coordinate_bounds apos bpos product ab ac ba ca, ?_, ?_⟩
  · exact positive_product_coordinate_bounds bpos apos (by nlinarith [product]) ba bc ab cb
  · exact positive_product_coordinate_bounds cpos apos (by nlinarith [product]) ca cb ac bc

theorem realPositiveDiagonal_product {matrix : SpecialLinearGroup (Fin 3) ℝ}
    (diagonal : realPositiveDiagonal (SpecialLinearGroup.toGL matrix)) :
    matrix.val 0 0 * matrix.val 1 1 * matrix.val 2 2 = 1 := by
  have determinant := Matrix.SpecialLinearGroup.det_coe matrix
  change (SpecialLinearGroup.toGL matrix).val.det = 1 at determinant
  rw [realPositiveDiagonal_val diagonal] at determinant
  simpa [Matrix.det_diagonal, Fin.prod_univ_three, mul_assoc] using determinant

theorem realSpecialDiagonalBox_of_ratios {matrix : SpecialLinearGroup (Fin 3) ℝ}
    (diagonal : realPositiveDiagonal (SpecialLinearGroup.toGL matrix))
    (ratio01 : 1 / 2 ≤ matrix.val 0 0 / matrix.val 1 1 ∧ matrix.val 0 0 / matrix.val 1 1 ≤ 8)
    (ratio12 : 1 / 2 ≤ matrix.val 1 1 / matrix.val 2 2 ∧ matrix.val 1 1 / matrix.val 2 2 ≤ 8) :
    matrix ∈ realSpecialDiagonalBox (1 / 64) 64 := by
  obtain ⟨first, second, third⟩ := positive_triple_ratio_bounds
    (diagonal.2 0) (diagonal.2 1) (diagonal.2 2) (realPositiveDiagonal_product diagonal) ratio01 ratio12
  refine ⟨fun index => matrix.val index index, ?_, (realPositiveDiagonal_val diagonal).symm⟩
  intro index
  fin_cases index
  · exact first
  · exact second
  · exact third

theorem real_ratio_power_bin {ratio : ℝ} (lower : 1 / 2 ≤ ratio) :
    ∃ index : ℕ, 1 / 2 ≤ ratio / (8 : ℝ) ^ index ∧ ratio / (8 : ℝ) ^ index ≤ 8 := by
  by_cases large : 1 ≤ ratio
  · obtain ⟨index, lower_power, upper_power⟩ := exists_nat_pow_near large (by norm_num : (1 : ℝ) < 8)
    refine ⟨index, ?_, ?_⟩
    · have bound : 1 ≤ ratio / (8 : ℝ) ^ index := (le_div_iff₀ (by positivity)).mpr (by simpa using lower_power)
      linarith
    · apply (div_le_iff₀ (by positivity)).mpr
      rw [pow_succ] at upper_power
      linarith
  · refine ⟨0, ?_, ?_⟩ <;> simp only [pow_zero, div_one]
    · exact lower
    · linarith

theorem realPositiveDiagonal_mul_ratio {first second : RealGL3}
    (first_diagonal : realPositiveDiagonal first) (second_diagonal : realPositiveDiagonal second)
    (row column : Fin 3) :
    (first * second).val row row / (first * second).val column column =
      (first.val row row / first.val column column) * (second.val row row / second.val column column) := by
  rw [realPositiveDiagonal_mul_val first_diagonal second_diagonal]
  simp only [Matrix.diagonal_apply_eq]
  exact mul_div_mul_comm _ _ _ _

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
