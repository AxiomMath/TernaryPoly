module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Special.LinearBoxes

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

noncomputable def realSpecialScaling (m n : ℤ) : SpecialLinearGroup (Fin 3) ℝ :=
  ⟨!![(2 : ℝ) ^ (2 * m + n), 0, 0; 0, (2 : ℝ) ^ (-m + n), 0;
      0, 0, (2 : ℝ) ^ (-m - 2 * n)], by
    simp only [Matrix.det_fin_three]
    change (2 : ℝ) ^ (2 * m + n) * (2 : ℝ) ^ (-m + n) * (2 : ℝ) ^ (-m - 2 * n) -
      (2 : ℝ) ^ (2 * m + n) * 0 * 0 - 0 * 0 * (2 : ℝ) ^ (-m - 2 * n) +
      0 * 0 * 0 + 0 * 0 * 0 - 0 * (2 : ℝ) ^ (-m + n) * 0 = 1
    simp only [mul_zero, zero_mul, sub_zero, add_zero]
    rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    have exponent : 2 * m + n + (-m + n) + (-m - 2 * n) = 0 := by ring
    rw [exponent, zpow_zero]⟩

theorem realSpecialScaling_positive (m n : ℤ) :
    realPositiveDiagonal (SpecialLinearGroup.toGL (realSpecialScaling m n)) := by
  constructor
  · intro row column different
    fin_cases row <;> fin_cases column <;> simp_all [realSpecialScaling]
  · intro index
    fin_cases index <;> change 0 < (2 : ℝ) ^ (_ : ℤ) <;> positivity

theorem realSpecialScaling_zero : realSpecialScaling 0 0 = 1 := by
  apply Subtype.ext
  ext row column
  fin_cases row <;> fin_cases column <;> norm_num [realSpecialScaling]

theorem realSpecialScaling_mul (m n m' n' : ℤ) :
    realSpecialScaling m n * realSpecialScaling m' n' = realSpecialScaling (m + m') (n + n') := by
  apply Subtype.ext
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [realSpecialScaling, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_three,
      ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)] <;> ring

theorem realSpecialScaling_inv (m n : ℤ) :
    (realSpecialScaling m n)⁻¹ = realSpecialScaling (-m) (-n) := by
  apply inv_eq_of_mul_eq_one_right
  rw [realSpecialScaling_mul, add_neg_cancel, add_neg_cancel, realSpecialScaling_zero]

theorem realSpecialScaling_ratio01 (m n : ℤ) :
    (realSpecialScaling m n).val 0 0 / (realSpecialScaling m n).val 1 1 = (8 : ℝ) ^ m := by
  change (2 : ℝ) ^ (2 * m + n) / (2 : ℝ) ^ (-m + n) = _
  rw [← zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0)]
  have exponent : 2 * m + n - (-m + n) = 3 * m := by ring
  rw [exponent, _root_.zpow_mul]
  norm_num

theorem realSpecialScaling_ratio12 (m n : ℤ) :
    (realSpecialScaling m n).val 1 1 / (realSpecialScaling m n).val 2 2 = (8 : ℝ) ^ n := by
  change (2 : ℝ) ^ (-m + n) / (2 : ℝ) ^ (-m - 2 * n) = _
  rw [← zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0)]
  have exponent : -m + n - (-m - 2 * n) = 3 * n := by ring
  rw [exponent, _root_.zpow_mul]
  norm_num

theorem realSpecialScaling_ratio02 (m n : ℤ) :
    (realSpecialScaling m n).val 0 0 / (realSpecialScaling m n).val 2 2 = (8 : ℝ) ^ (m + n) := by
  change (2 : ℝ) ^ (2 * m + n) / (2 : ℝ) ^ (-m - 2 * n) = _
  rw [← zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0)]
  have exponent : 2 * m + n - (-m - 2 * n) = 3 * (m + n) := by ring
  rw [exponent, _root_.zpow_mul]
  norm_num

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
