module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Scalar.DifferenceGrowth
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Scalar.BoundaryBounds

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix Filter

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

theorem normalized_scalar_difference_compact_power_bound
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family)
    (parameters : Set ℂ) (matrices : Set AdelicGL)
    (parameters_compact : IsCompact parameters) (matrices_compact : IsCompact matrices)
    (nonnegative : ∀ parameter ∈ parameters, 0 ≤ 3 / 2 + parameter.re)
    (integral : ∀ matrix ∈ matrices, finiteGroup matrix ∈ Set.range (GeneralLinearGroup.map integralEmbedding)) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ shift : AdelicGL, ∀ epsilon : ℝ, 0 ≤ epsilon →
      (∀ parameter ∈ parameters, ∀ matrix : AdelicGL, inMaximalCompact matrix →
        ‖normalizedScalarDifferenceProfile flat shift parameter matrix‖ ≤ epsilon) →
      ∀ parameter ∈ parameters, ∀ matrix ∈ matrices, ∀ flag,
        ‖normalizedScalarDifferenceProfile flat shift parameter (rationalGroup flag.out⁻¹ * matrix)‖ ≤
          ‖(fun index => (planeFlagIntegerRow flag index : ℝ))‖ ^ (-(3 / 2 + parameter.re)) * (bound * epsilon) := by
  obtain ⟨translationBound, translation_positive, translated⟩ := real_row_translate_compact_bound
    (realGroup '' matrices) (matrices_compact.image realGroup_continuous)
  let coefficient (input : ℂ × AdelicGL) : ℝ := Real.exp ((inductionExponent .plane input.1).re *
    Real.log |(realGroup input.2).val.det| +
      (3 / 2 + input.1.re) * Real.log translationBound)
  have exponent_continuous : Continuous (fun parameter : ℂ => (inductionExponent .plane parameter).re) :=
    Complex.continuous_re.comp (continuous_const.add (continuous_id.div_const 3))
  have log_continuous := real_log_abs_det_continuous
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
  refine ⟨uniformBound, le_max_left _ _, ?_⟩
  intro shift epsilon epsilon_nonnegative bounded parameter parameter_in matrix matrix_in flag
  have parameter_nonnegative := nonnegative parameter parameter_in
  have replacement := normalizedScalarDifferenceProfile_norm_of_representative flat shift parameter
    (integralRational (planeFlagIntegralMatrix flag)) matrix
  rw [planeFlagIntegralMatrix_spec] at replacement
  rw [replacement]
  let representative := rationalGroup ((integralRational (planeFlagIntegralMatrix flag))⁻¹)
  have representative_integral : finiteGroup representative ∈
      Set.range (GeneralLinearGroup.map integralEmbedding) := by
    simpa only [representative, map_inv] using integral_rational_finite_integral (planeFlagIntegralMatrix flag)⁻¹
  have real_representative_det : |(realGroup representative).val.det| = 1 := by
    simpa only [representative, map_inv] using integralRational_real_abs_det (planeFlagIntegralMatrix flag)⁻¹
  have determinant_norm : |(realGroup (representative * matrix)).val.det| = |(realGroup matrix).val.det| := by
    rw [map_mul]
    change |((realGroup representative).val * (realGroup matrix).val).det| = _
    rw [Matrix.det_mul, abs_mul, real_representative_det, one_mul]
  have finite_member : finiteGroup (representative * matrix) ∈ Set.range (GeneralLinearGroup.map integralEmbedding) := by
    obtain ⟨first, first_eq⟩ := representative_integral
    obtain ⟨second, second_eq⟩ := integral matrix matrix_in
    exact ⟨first * second, by rw [map_mul, first_eq, second_eq, map_mul]⟩
  have bound_at : ‖normalizedScalarDifferenceProfile flat shift parameter (representative * matrix)‖ ≤
      Real.exp ((inductionExponent .plane parameter).re * Real.log |(realGroup matrix).val.det| -
        (3 / 2 + parameter.re) * Real.log (realPlaneHeight (realGroup (representative * matrix)))) * epsilon := by
    obtain ⟨compactMatrix, orthogonal, reduction⟩ := normalizedScalarDifferenceProfile_real_compact_reduction flat shift (representative * matrix)
    rw [reduction parameter, determinant_norm]
    apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
    apply bounded parameter parameter_in
    rw [combineGL_eq_real_finite]
    exact orthogonal_integral_compact _ _ orthogonal finite_member
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
      Real.log |(realGroup matrix).val.det| -
        (3 / 2 + parameter.re) * Real.log height ≤
      Real.log rowNorm * (-(3 / 2 + parameter.re)) +
        ((inductionExponent .plane parameter).re * Real.log |(realGroup matrix).val.det| +
          (3 / 2 + parameter.re) * Real.log translationBound) := by
    nlinarith [mul_le_mul_of_nonneg_left log_row parameter_nonnegative]
  calc
    _ ≤ Real.exp ((inductionExponent .plane parameter).re *
        Real.log |(realGroup matrix).val.det| -
          (3 / 2 + parameter.re) * Real.log height) * epsilon := bound_at
    _ ≤ Real.exp (Real.log rowNorm * (-(3 / 2 + parameter.re)) +
        ((inductionExponent .plane parameter).re * Real.log |(realGroup matrix).val.det| +
          (3 / 2 + parameter.re) * Real.log translationBound)) * epsilon :=
      mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr exponent_bound) epsilon_nonnegative
    _ = rowNorm ^ (-(3 / 2 + parameter.re)) * (coefficient (parameter, matrix) * epsilon) := by
      rw [Real.exp_add, ← Real.rpow_def_of_pos row_positive]
      exact mul_assoc _ _ _
    _ ≤ rowNorm ^ (-(3 / 2 + parameter.re)) * (uniformBound * epsilon) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (coefficient_bound parameter parameter_in matrix matrix_in) epsilon_nonnegative)
        (Real.rpow_nonneg (norm_nonneg _) _)

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
