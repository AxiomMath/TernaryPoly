module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.IntegerRowSummability
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Normalized.RationalNorms

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem planeFlagIntegerRow_norm_ge_one (flag : Flags .plane) :
    1 ≤ ‖(fun index => (planeFlagIntegerRow flag index : ℝ))‖ := by
  have exists_entry : ∃ index, planeFlagIntegerRow flag index ≠ 0 := by
    by_contra! zero
    exact planeFlagIntegerRow_ne_zero flag (funext zero)
  obtain ⟨index, nonzero⟩ := exists_entry
  have entry_bound : (1 : ℝ) ≤ ‖(planeFlagIntegerRow flag index : ℝ)‖ := by
    rw [Real.norm_eq_abs, ← Int.cast_abs]
    exact_mod_cast Int.one_le_abs nonzero
  exact entry_bound.trans (norm_le_pi_norm (fun index => (planeFlagIntegerRow flag index : ℝ)) index)

theorem planeFlagIntegerRow_norm_le_height (flag : Flags .plane) :
    ‖(fun index => (planeFlagIntegerRow flag index : ℝ))‖ ≤
      realPlaneHeight (realGroup (rationalGroup ((integralRational (planeFlagIntegralMatrix flag))⁻¹))) := by
  have height_eq :
      realPlaneHeight (realGroup (rationalGroup ((integralRational (planeFlagIntegralMatrix flag))⁻¹))) =
        Real.sqrt ((planeFlagIntegerRow flag 0 : ℝ) ^ 2 +
          (planeFlagIntegerRow flag 1 : ℝ) ^ 2 + (planeFlagIntegerRow flag 2 : ℝ) ^ 2) := by
    rw [← integralRational.map_inv (planeFlagIntegralMatrix flag)]
    change Real.sqrt (((((planeFlagIntegralMatrix flag).inv 2 0 : ℤ) : ℚ) : ℝ) ^ 2 +
      (((((planeFlagIntegralMatrix flag).inv 2 1 : ℤ) : ℚ) : ℝ)) ^ 2 +
      (((((planeFlagIntegralMatrix flag).inv 2 2 : ℤ) : ℚ) : ℝ)) ^ 2) = _
    push_cast
    rfl
  rw [height_eq]
  apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
  intro index
  rw [Real.norm_eq_abs]
  apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [sq_abs, Real.sq_sqrt (by positivity)]
  have square_bound : (planeFlagIntegerRow flag index : ℝ) ^ 2 ≤
      ∑ coordinate : Fin 3, (planeFlagIntegerRow flag coordinate : ℝ) ^ 2 :=
    Finset.single_le_sum (fun coordinate _ => sq_nonneg (planeFlagIntegerRow flag coordinate : ℝ))
      (Finset.mem_univ index)
  simpa only [Fin.sum_univ_three] using square_bound

theorem normalized_flag_norm_bound
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ parameter : ℂ, -(3 / 2 : ℝ) ≤ parameter.re → ∀ flag : Flags .plane,
      ‖(normalizedCuspVector flat.1 parameter (rationalGroup flag.out⁻¹)).val‖ ≤
        ‖(fun index => (planeFlagIntegerRow flag index : ℝ))‖ ^ (-(3 / 2 + parameter.re)) * bound := by
  obtain ⟨bound, nonnegative, bounded⟩ := normalizedCuspVector_integral_finite_norm_bound flat
  refine ⟨bound, nonnegative, ?_⟩
  intro parameter large flag
  have replacement := normalizedCuspVector_norm_of_representative flat.1 parameter
    (integralRational (planeFlagIntegralMatrix flag)) 1
  simp only [mul_one, planeFlagIntegralMatrix_spec] at replacement
  rw [replacement]
  have integral : finiteGroup (rationalGroup ((integralRational (planeFlagIntegralMatrix flag))⁻¹)) ∈
      Set.range (GeneralLinearGroup.map integralEmbedding) := by
    simpa only [map_inv] using integral_rational_finite_integral (planeFlagIntegralMatrix flag)⁻¹
  have determinant_norm : adeleNorm (GeneralLinearGroup.det
      (rationalGroup ((integralRational (planeFlagIntegralMatrix flag))⁻¹))) = 1 := by
    rw [rationalGroup, GeneralLinearGroup.map_det, adeleNorm_rational]
  have bound_at := bounded parameter _ integral
  rw [determinant_norm, NNReal.coe_one, Real.log_one, mul_zero, zero_sub] at bound_at
  have height_bound : ‖(normalizedCuspVector flat.1 parameter
      (rationalGroup ((integralRational (planeFlagIntegralMatrix flag))⁻¹))).val‖ ≤
      realPlaneHeight (realGroup (rationalGroup ((integralRational (planeFlagIntegralMatrix flag))⁻¹))) ^
        (-(3 / 2 + parameter.re)) * bound := by
    rw [Real.rpow_def_of_pos (realPlaneHeight_pos _)]
    convert bound_at using 2
    congr 1
    ring
  exact height_bound.trans (mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le zero_lt_one (planeFlagIntegerRow_norm_ge_one flag))
      (planeFlagIntegerRow_norm_le_height flag) (by linarith)) nonnegative)

theorem normalized_flag_norm_summable
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (parameter : ℂ) (large : 3 / 2 < parameter.re) :
    Summable (fun flag : Flags .plane =>
      ‖(normalizedCuspVector flat.1 parameter (rationalGroup flag.out⁻¹)).val‖) := by
  obtain ⟨bound, _, bounded⟩ := normalized_flag_norm_bound flat
  apply ((planeFlagIntegerRow_summable (-(3 / 2 + parameter.re)) (by linarith)).mul_right bound).of_nonneg_of_le
    (fun _ => norm_nonneg _)
  intro flag
  exact bounded parameter (by linarith) flag

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
