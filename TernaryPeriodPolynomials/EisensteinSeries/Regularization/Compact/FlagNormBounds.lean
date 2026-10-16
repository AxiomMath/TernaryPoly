module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.TranslatedFlagNormBounds

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem normalized_flag_compact_summable_majorant
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family)
    (parameters : Set ℂ) (matrices : Set AdelicGL)
    (parameters_compact : IsCompact parameters) (matrices_compact : IsCompact matrices)
    (large : ∀ parameter ∈ parameters, 3 / 2 < parameter.re)
    (integral : ∀ matrix ∈ matrices,
      finiteGroup matrix ∈ Set.range (GeneralLinearGroup.map integralEmbedding)) :
    ∃ majorant : Flags .plane → ℝ, Summable majorant ∧
      ∀ parameter ∈ parameters, ∀ matrix ∈ matrices, ∀ flag,
        ‖(normalizedCuspVector flat.1 parameter (rationalGroup flag.out⁻¹ * matrix)).val‖ ≤ majorant flag := by
  rcases Set.eq_empty_or_nonempty parameters with empty | nonempty
  · subst parameters
    exact ⟨fun _ => 0, summable_zero, by simp⟩
  obtain ⟨lower, lower_in, minimum⟩ :=
    parameters_compact.exists_isMinOn nonempty Complex.continuous_re.continuousOn
  obtain ⟨compactBound, compact_nonnegative, bounded⟩ := normalizedCuspVector_integral_finite_norm_bound flat
  obtain ⟨translationBound, translation_positive, translated⟩ := real_row_translate_compact_bound
    (realGroup '' matrices) (matrices_compact.image realGroup_continuous)
  let coefficient (input : ℂ × AdelicGL) : ℝ := Real.exp ((inductionExponent .plane input.1).re *
    Real.log (adeleNorm (GeneralLinearGroup.det input.2) : ℝ) +
      (3 / 2 + input.1.re) * Real.log translationBound)
  have exponent_continuous : Continuous (fun parameter : ℂ => (inductionExponent .plane parameter).re) :=
    Complex.continuous_re.comp (continuous_const.add (continuous_id.div_const 3))
  have determinant_continuous := NNReal.continuous_coe.comp (adeleNorm_continuous.comp adelicDet_continuous)
  have log_continuous := determinant_continuous.log
    (fun matrix => ne_of_gt (NNReal.coe_pos.mpr (adeleNorm_pos (GeneralLinearGroup.det matrix))))
  have coefficient_continuous : Continuous coefficient :=
    (((exponent_continuous.comp continuous_fst).mul (log_continuous.comp continuous_snd)).add
      ((continuous_const.add (Complex.continuous_re.comp continuous_fst)).mul continuous_const)).rexp
  obtain ⟨coefficientBound, coefficient_bounded⟩ :=
    (parameters_compact.prod matrices_compact).exists_bound_of_continuousOn coefficient_continuous.continuousOn
  let uniformBound := max 0 coefficientBound
  have coefficient_bound (parameter : ℂ) (parameter_in : parameter ∈ parameters)
      (matrix : AdelicGL) (matrix_in : matrix ∈ matrices) : coefficient (parameter, matrix) ≤ uniformBound := by
    have value_bound := coefficient_bounded (parameter, matrix) ⟨parameter_in, matrix_in⟩
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at value_bound
    exact value_bound.trans (le_max_right _ _)
  refine ⟨fun flag => ‖(fun index => (planeFlagIntegerRow flag index : ℝ))‖ ^
    (-(3 / 2 + lower.re)) * (uniformBound * compactBound),
    (planeFlagIntegerRow_summable (-(3 / 2 + lower.re)) (by linarith [large lower lower_in])).mul_right _, ?_⟩
  intro parameter parameter_in matrix matrix_in flag
  have parameter_large := large parameter parameter_in
  have replacement := normalizedCuspVector_norm_of_representative flat.1 parameter
    (integralRational (planeFlagIntegralMatrix flag)) matrix
  rw [planeFlagIntegralMatrix_spec] at replacement
  rw [replacement]
  let representative := rationalGroup ((integralRational (planeFlagIntegralMatrix flag))⁻¹)
  have representative_integral : finiteGroup representative ∈
      Set.range (GeneralLinearGroup.map integralEmbedding) := by
    simpa only [representative, map_inv] using integral_rational_finite_integral (planeFlagIntegralMatrix flag)⁻¹
  have determinant_norm : adeleNorm (GeneralLinearGroup.det (representative * matrix)) =
      adeleNorm (GeneralLinearGroup.det matrix) := by
    simp only [representative, map_mul, rationalGroup, GeneralLinearGroup.map_det, adeleNorm_rational, one_mul]
  have bound_at := bounded parameter (representative * matrix)
    (finite_integral_mul representative_integral (integral matrix matrix_in))
  rw [determinant_norm] at bound_at
  let height := realPlaneHeight (realGroup (representative * matrix))
  let rowNorm := ‖(fun index => (planeFlagIntegerRow flag index : ℝ))‖
  have row_positive : 0 < rowNorm := lt_of_lt_of_le zero_lt_one (planeFlagIntegerRow_norm_ge_one flag)
  have height_positive : 0 < height := realPlaneHeight_pos _
  have row_bound : rowNorm ≤ translationBound * height := by
    dsimp only [rowNorm, height]
    rw [planeFlagIntegerRow_real, map_mul]
    exact translated (realGroup matrix) ⟨matrix, matrix_in, rfl⟩ (realGroup representative)
  have log_row : Real.log rowNorm ≤ Real.log translationBound + Real.log height := by
    rw [← Real.log_mul (ne_of_gt translation_positive) (ne_of_gt height_positive)]
    exact Real.log_le_log row_positive row_bound
  have exponent_bound : (inductionExponent .plane parameter).re *
      Real.log (adeleNorm (GeneralLinearGroup.det matrix) : ℝ) -
        (3 / 2 + parameter.re) * Real.log height ≤
      Real.log rowNorm * (-(3 / 2 + parameter.re)) +
        ((inductionExponent .plane parameter).re * Real.log (adeleNorm (GeneralLinearGroup.det matrix) : ℝ) +
          (3 / 2 + parameter.re) * Real.log translationBound) := by
    nlinarith [mul_le_mul_of_nonneg_left log_row (show 0 ≤ 3 / 2 + parameter.re by linarith)]
  have real_minimum : lower.re ≤ parameter.re := minimum parameter_in
  have row_power_bound : rowNorm ^ (-(3 / 2 + parameter.re)) ≤ rowNorm ^ (-(3 / 2 + lower.re)) :=
    Real.rpow_le_rpow_of_exponent_le (planeFlagIntegerRow_norm_ge_one flag)
      (by linarith)
  calc
    _ ≤ Real.exp ((inductionExponent .plane parameter).re *
        Real.log (adeleNorm (GeneralLinearGroup.det matrix) : ℝ) -
          (3 / 2 + parameter.re) * Real.log height) * compactBound := bound_at
    _ ≤ Real.exp (Real.log rowNorm * (-(3 / 2 + parameter.re)) +
        ((inductionExponent .plane parameter).re * Real.log (adeleNorm (GeneralLinearGroup.det matrix) : ℝ) +
          (3 / 2 + parameter.re) * Real.log translationBound)) * compactBound :=
      mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr exponent_bound) compact_nonnegative
    _ = rowNorm ^ (-(3 / 2 + parameter.re)) * (coefficient (parameter, matrix) * compactBound) := by
      rw [Real.exp_add, ← Real.rpow_def_of_pos row_positive]
      exact mul_assoc _ _ _
    _ ≤ rowNorm ^ (-(3 / 2 + lower.re)) * (uniformBound * compactBound) :=
      mul_le_mul row_power_bound
        (mul_le_mul_of_nonneg_right (coefficient_bound parameter parameter_in matrix matrix_in) compact_nonnegative)
        (mul_nonneg (Real.exp_nonneg _) compact_nonnegative) (Real.rpow_nonneg (norm_nonneg _) _)

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
