module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Real.RowTranslation

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem normalized_flag_norm_bound_integral_finite
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (matrix : AdelicGL)
    (integral : finiteGroup matrix ∈ Set.range (GeneralLinearGroup.map integralEmbedding))
    (parameter : ℂ) (large : -(3 / 2 : ℝ) ≤ parameter.re) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ flag : Flags .plane,
      ‖(normalizedCuspVector flat.1 parameter (rationalGroup flag.out⁻¹ * matrix)).val‖ ≤
        ‖(fun index => (planeFlagIntegerRow flag index : ℝ))‖ ^ (-(3 / 2 + parameter.re)) * bound := by
  obtain ⟨compactBound, compact_nonnegative, bounded⟩ := normalizedCuspVector_integral_finite_norm_bound flat
  obtain ⟨translationBound, translation_positive, translated⟩ := real_row_translate_bound (realGroup matrix)
  let coefficient : ℝ := Real.exp ((inductionExponent .plane parameter).re *
    Real.log (adeleNorm (GeneralLinearGroup.det matrix) : ℝ) +
      (3 / 2 + parameter.re) * Real.log translationBound)
  refine ⟨coefficient * compactBound, mul_nonneg (Real.exp_nonneg _) compact_nonnegative, ?_⟩
  intro flag
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
  have bound_at := bounded parameter (representative * matrix) (finite_integral_mul representative_integral integral)
  rw [determinant_norm] at bound_at
  let height := realPlaneHeight (realGroup (representative * matrix))
  let rowNorm := ‖(fun index => (planeFlagIntegerRow flag index : ℝ))‖
  have row_positive : 0 < rowNorm := lt_of_lt_of_le zero_lt_one (planeFlagIntegerRow_norm_ge_one flag)
  have height_positive : 0 < height := realPlaneHeight_pos _
  have row_bound : rowNorm ≤ translationBound * height := by
    dsimp only [rowNorm, height]
    rw [planeFlagIntegerRow_real, map_mul]
    exact translated (realGroup representative)
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
  calc
    _ ≤ Real.exp ((inductionExponent .plane parameter).re *
        Real.log (adeleNorm (GeneralLinearGroup.det matrix) : ℝ) -
          (3 / 2 + parameter.re) * Real.log height) * compactBound := bound_at
    _ ≤ Real.exp (Real.log rowNorm * (-(3 / 2 + parameter.re)) +
        ((inductionExponent .plane parameter).re * Real.log (adeleNorm (GeneralLinearGroup.det matrix) : ℝ) +
          (3 / 2 + parameter.re) * Real.log translationBound)) * compactBound :=
      mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr exponent_bound) compact_nonnegative
    _ = _ := by
      rw [Real.exp_add, ← Real.rpow_def_of_pos row_positive]
      exact mul_assoc _ _ _

theorem normalized_flag_norm_summable_integral_finite
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (matrix : AdelicGL)
    (integral : finiteGroup matrix ∈ Set.range (GeneralLinearGroup.map integralEmbedding))
    (parameter : ℂ) (large : 3 / 2 < parameter.re) :
    Summable (fun flag : Flags .plane =>
      ‖(normalizedCuspVector flat.1 parameter (rationalGroup flag.out⁻¹ * matrix)).val‖) := by
  obtain ⟨bound, _, bounded⟩ := normalized_flag_norm_bound_integral_finite flat matrix integral parameter (by linarith)
  exact ((planeFlagIntegerRow_summable (-(3 / 2 + parameter.re)) (by linarith)).mul_right bound).of_nonneg_of_le
    (fun _ => norm_nonneg _) bounded

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
