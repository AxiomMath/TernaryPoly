module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Normalized.FlagNormBounds

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem real_row_norm_le_height (matrix : RealGL3) : ‖matrix.val 2‖ ≤ realPlaneHeight matrix := by
  apply (pi_norm_le_iff_of_nonneg (realPlaneHeight_pos matrix).le).mpr
  intro index
  rw [Real.norm_eq_abs]
  apply (sq_le_sq₀ (abs_nonneg _) (realPlaneHeight_pos matrix).le).mp
  rw [sq_abs, realPlaneHeight_sq]
  have square_bound : matrix.val 2 index ^ 2 ≤ ∑ coordinate : Fin 3, matrix.val 2 coordinate ^ 2 :=
    Finset.single_le_sum (fun coordinate _ => sq_nonneg (matrix.val 2 coordinate)) (Finset.mem_univ index)
  simpa only [Fin.sum_univ_three] using square_bound

theorem real_row_translate_bound (translation : RealGL3) :
    ∃ bound : ℝ, 0 < bound ∧ ∀ matrix : RealGL3,
      ‖matrix.val 2‖ ≤ bound * realPlaneHeight (matrix * translation) := by
  let inverseAction : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) :=
    LinearMap.toContinuousLinearMap translation.inv.vecMulLinear
  refine ⟨max 1 ‖inverseAction‖, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro matrix
  have inverse_value : inverseAction ((matrix * translation).val 2) = matrix.val 2 := by
    change Matrix.vecMul ((matrix.val * translation.val) 2) translation.inv = matrix.val 2
    have row_product : (matrix.val * translation.val) 2 = Matrix.vecMul (matrix.val 2) translation.val := rfl
    rw [row_product, Matrix.vecMul_vecMul, translation.val_inv, Matrix.vecMul_one]
  calc
    ‖matrix.val 2‖ = ‖inverseAction ((matrix * translation).val 2)‖ := congrArg norm inverse_value.symm
    _ ≤ ‖inverseAction‖ * ‖(matrix * translation).val 2‖ := inverseAction.le_opNorm _
    _ ≤ max 1 ‖inverseAction‖ * realPlaneHeight (matrix * translation) :=
      mul_le_mul (le_max_right _ _) (real_row_norm_le_height _) (norm_nonneg _)
        (le_trans (by norm_num : (0 : ℝ) ≤ 1) (le_max_left _ _))

theorem planeFlagIntegerRow_real (flag : Flags .plane) :
    (fun index => (planeFlagIntegerRow flag index : ℝ)) =
      (realGroup (rationalGroup ((integralRational (planeFlagIntegralMatrix flag))⁻¹))).val 2 := by
  rw [← integralRational.map_inv (planeFlagIntegralMatrix flag)]
  funext index
  change ((planeFlagIntegralMatrix flag).inv 2 index : ℝ) =
    ((((planeFlagIntegralMatrix flag).inv 2 index : ℤ) : ℚ) : ℝ)
  norm_cast

theorem real_row_inverse_action_continuous :
    Continuous (fun translation : RealGL3 =>
      LinearMap.toContinuousLinearMap translation.inv.vecMulLinear) := by
  apply continuous_clm_apply.mpr
  intro row
  change Continuous (fun translation : RealGL3 => Matrix.vecMul row translation.inv)
  exact continuous_const.matrix_vecMul (Units.continuous_val.comp continuous_inv)

theorem real_row_translate_compact_bound
    (translations : Set RealGL3) (compact : IsCompact translations) :
    ∃ bound : ℝ, 0 < bound ∧ ∀ translation ∈ translations, ∀ matrix : RealGL3,
      ‖matrix.val 2‖ ≤ bound * realPlaneHeight (matrix * translation) := by
  obtain ⟨bound, bounded⟩ := compact.exists_bound_of_continuousOn
    real_row_inverse_action_continuous.continuousOn
  refine ⟨max 1 bound, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro translation member matrix
  let inverseAction : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) :=
    LinearMap.toContinuousLinearMap translation.inv.vecMulLinear
  have inverse_value : inverseAction ((matrix * translation).val 2) = matrix.val 2 := by
    change Matrix.vecMul ((matrix.val * translation.val) 2) translation.inv = matrix.val 2
    have row_product : (matrix.val * translation.val) 2 = Matrix.vecMul (matrix.val 2) translation.val := rfl
    rw [row_product, Matrix.vecMul_vecMul, translation.val_inv, Matrix.vecMul_one]
  calc
    ‖matrix.val 2‖ = ‖inverseAction ((matrix * translation).val 2)‖ := congrArg norm inverse_value.symm
    _ ≤ ‖inverseAction‖ * ‖(matrix * translation).val 2‖ := inverseAction.le_opNorm _
    _ ≤ max 1 bound * realPlaneHeight (matrix * translation) :=
      mul_le_mul ((bounded translation member).trans (le_max_right _ _))
        (real_row_norm_le_height _) (norm_nonneg _)
        (le_trans (by norm_num : (0 : ℝ) ≤ 1) (le_max_left _ _))

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
