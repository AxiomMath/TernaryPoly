module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Real.DiagonalScaling
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Real.RowTranslation

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

theorem real_compact_inverse_row_bound (matrices : Set RealGL3) (compact : IsCompact matrices) :
    ∃ bound : ℝ, 0 < bound ∧ ∀ matrix ∈ matrices, ∀ row : Fin 3 → ℝ,
      ‖row‖ ≤ bound * ‖row ᵥ* matrix.val‖ := by
  obtain ⟨bound, bounded⟩ := compact.exists_bound_of_continuousOn
    real_row_inverse_action_continuous.continuousOn
  refine ⟨max 1 bound, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro matrix member row
  let inverseAction : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) :=
    LinearMap.toContinuousLinearMap matrix.inv.vecMulLinear
  have inverse_value : inverseAction (row ᵥ* matrix.val) = row := by
    change (row ᵥ* matrix.val) ᵥ* matrix.inv = row
    rw [Matrix.vecMul_vecMul, matrix.val_inv, Matrix.vecMul_one]
  calc
    ‖row‖ = ‖inverseAction (row ᵥ* matrix.val)‖ := congrArg norm inverse_value.symm
    _ ≤ ‖inverseAction‖ * ‖row ᵥ* matrix.val‖ := inverseAction.le_opNorm _
    _ ≤ max 1 bound * ‖row ᵥ* matrix.val‖ :=
      mul_le_mul_of_nonneg_right ((bounded matrix member).trans (le_max_right _ _)) (norm_nonneg _)

theorem realSpecialScaling_inverse_row_bound (m n : ℕ) (row : Fin 3 → ℝ) :
    ‖row ᵥ* (SpecialLinearGroup.toGL (realSpecialScaling m n)⁻¹).val‖ ≤
      (2 : ℝ) ^ (m + 2 * n) * ‖row‖ := by
  rw [realSpecialScaling_inv]
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro index
  have power_bound (exponent : ℤ) (bound : exponent ≤ (m : ℤ) + 2 * n) :
      (2 : ℝ) ^ exponent ≤ (2 : ℝ) ^ (m + 2 * n) := by
    have h := zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) bound
    have cast : ((m + 2 * n : ℕ) : ℤ) = (m : ℤ) + 2 * n := by omega
    rw [← cast, zpow_natCast] at h
    exact h
  have coordinate_bound (exponent : ℤ) (bound : exponent ≤ (m : ℤ) + 2 * n) :
      ‖row index * (2 : ℝ) ^ exponent‖ ≤ (2 : ℝ) ^ (m + 2 * n) * ‖row‖ := by
    rw [norm_mul, Real.norm_of_nonneg (by positivity : 0 ≤ (2 : ℝ) ^ exponent)]
    exact (mul_le_mul (norm_le_pi_norm row index) (power_bound exponent bound) (by positivity) (norm_nonneg row)).trans_eq (mul_comm _ _)
  fin_cases index <;>
    simpa [realSpecialScaling, Matrix.vecMul, dotProduct, Fin.sum_univ_three] using
      coordinate_bound _ (by omega)

theorem realSpecialScaling_row_bound (m n : ℕ) (row : Fin 3 → ℝ) :
    ‖row‖ ≤ (2 : ℝ) ^ (m + 2 * n) * ‖row ᵥ* (SpecialLinearGroup.toGL (realSpecialScaling m n)).val‖ := by
  have bound := realSpecialScaling_inverse_row_bound m n
    (row ᵥ* (SpecialLinearGroup.toGL (realSpecialScaling m n)).val)
  have inverse_identity : (SpecialLinearGroup.toGL (realSpecialScaling m n)).val *
      (SpecialLinearGroup.toGL (realSpecialScaling m n)⁻¹).val = 1 := by
    rw [map_inv]
    exact (SpecialLinearGroup.toGL (realSpecialScaling m n)).val_inv
  simpa only [Matrix.vecMul_vecMul, inverse_identity, Matrix.vecMul_one] using bound

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
