module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.FlagSummability
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.MaximalCompact

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.RealRowBounds

theorem row_mul_bound (row : Fin 3 → ℝ) (matrix : Matrix (Fin 3) (Fin 3) ℝ) :
    ‖row ᵥ* matrix‖ ≤ 3 * ‖row‖ * ‖matrix‖ := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro column
  change ‖∑ index, row index * matrix index column‖ ≤ _
  calc
    ‖∑ index, row index * matrix index column‖ ≤ ∑ index, ‖row index * matrix index column‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _index : Fin 3, ‖row‖ * ‖matrix‖ := by
      apply Finset.sum_le_sum
      intro index _
      rw [norm_mul]
      exact mul_le_mul (norm_le_pi_norm row index)
        (Matrix.norm_entry_le_entrywise_sup_norm matrix) (norm_nonneg _) (norm_nonneg _)
    _ = 3 * ‖row‖ * ‖matrix‖ := by simp; ring

theorem row_recover_bound (row : Fin 3 → ℝ) (matrix : RealGL3) :
    ‖row‖ ≤ 3 * ‖row ᵥ* matrix.val‖ * ‖matrix.inv‖ := by
  have bound := row_mul_bound (row ᵥ* matrix.val) matrix.inv
  simpa only [Matrix.vecMul_vecMul, matrix.val_inv, Matrix.vecMul_one] using bound

theorem orthogonal_row_bound (matrix : RealGL3)
    (orthogonal : matrix.val.transpose * matrix.val = 1) (row : Fin 3) :
    ‖matrix.val row‖ ≤ 1 := by
  apply (pi_norm_le_iff_of_nonneg (by norm_num)).mpr
  intro column
  rw [Real.norm_eq_abs, abs_le]
  exact MaximalCompact.orthogonal_entry_bound matrix.val orthogonal row column

theorem scaled_orthogonal_row_bound (unit : ℝˣ) (matrix : RealGL3)
    (orthogonal : matrix.val.transpose * matrix.val = 1) (row : Fin 3) :
    ‖unit.val • matrix.val row‖ ≤ |unit.val| := by
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_of_le_one_right (abs_nonneg _) (orthogonal_row_bound matrix orthogonal row)

theorem plane_lastRow {R : Type} [CommRing R] (first second : R)
    (binary : GeneralLinearGroup (Fin 2) R) (unit : Rˣ) (matrix : GeneralLinearGroup (Fin 3) R) :
    (planeUnipotent first second * planeLevi binary unit * matrix).val 2 = unit.val • matrix.val 2 := by
  ext column
  fin_cases column <;>
    simp [planeUnipotent, planeLevi, planeBlock, Matrix.mul_apply, Fin.sum_univ_succ]

theorem decomposition_row_bound (row : Fin 3 → ℝ) (argument : RealGL3)
    (first second : ℝ) (binary : GeneralLinearGroup (Fin 2) ℝ) (unit : ℝˣ) (compact : RealGL3)
    (orthogonal : compact.val.transpose * compact.val = 1)
    (equality : row ᵥ* argument.val =
      (planeUnipotent first second * planeLevi binary unit * compact).val 2) :
    ‖row‖ ≤ 3 * |unit.val| * ‖argument.inv‖ := by
  have bound := row_recover_bound row argument
  rw [equality, plane_lastRow] at bound
  exact bound.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (scaled_orthogonal_row_bound unit compact orthogonal 2) (by norm_num))
    (norm_nonneg _))

theorem real_translate_summable (argument : RealGL3) (exponent : ℝ) (bound : exponent < -3) :
    Summable (fun flag : Flags .plane =>
      ‖(fun index => (IntegerRows.flagRow flag index : ℝ)) ᵥ* argument.val‖ ^ exponent) := by
  have inversePositive : 0 < ‖argument.inv‖ := by
    apply norm_pos_iff.mpr
    intro zero
    have identity := argument.inv_val
    rw [zero, zero_mul] at identity
    exact zero_ne_one identity
  let constant := (3 * ‖argument.inv‖) ^ (-exponent)
  apply Summable.of_nonneg_of_le (fun _ => Real.rpow_nonneg (norm_nonneg _) _) _
    ((FlagSummability.flagHeight_summable exponent bound).mul_left constant)
  intro flag
  have positive : 0 < FlagSummability.flagHeight flag := FlagSummability.flagHeight_pos flag
  have lower := row_recover_bound (fun index => (IntegerRows.flagRow flag index : ℝ)) argument
  have lower' : FlagSummability.flagHeight flag / (3 * ‖argument.inv‖) ≤
      ‖(fun index => (IntegerRows.flagRow flag index : ℝ)) ᵥ* argument.val‖ := by
    apply (div_le_iff₀ (mul_pos (by norm_num) inversePositive)).mpr
    simpa only [FlagSummability.flagHeight, mul_assoc, mul_comm, mul_left_comm] using lower
  have estimate := Real.rpow_le_rpow_of_nonpos
    (div_pos positive (mul_pos (by norm_num) inversePositive)) lower' (by linarith : exponent ≤ 0)
  rw [Real.div_rpow positive.le (by positivity), div_eq_mul_inv, ← Real.rpow_neg (by positivity)] at estimate
  simpa only [constant, mul_comm] using estimate

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.RealRowBounds
