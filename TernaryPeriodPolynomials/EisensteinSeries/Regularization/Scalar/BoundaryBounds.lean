module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.SectionScalarBounds
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Scalar.ProfileFlagBounds
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.LatticeBoundaryBounds

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix Filter

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem normalized_scalar_profile_compact_power_bound
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family)
    (parameters : Set ℂ) (matrices : Set AdelicGL)
    (parameters_compact : IsCompact parameters) (matrices_compact : IsCompact matrices)
    (nonnegative : ∀ parameter ∈ parameters, 0 ≤ 3 / 2 + parameter.re) :
    ∃ bound : ℝ, 0 ≤ bound ∧
      ∀ parameter ∈ parameters, ∀ matrix ∈ matrices, ∀ flag,
        ‖normalizedScalarProfile flat parameter (rationalGroup flag.out⁻¹ * matrix)‖ ≤
          ‖(fun index => (planeFlagIntegerRow flag index : ℝ))‖ ^ (-(3 / 2 + parameter.re)) * bound := by
  let finiteProducts : Set FiniteGL := (fun input : FiniteGL × AdelicGL => input.1 * finiteGroup input.2) ''
    (Set.range (GeneralLinearGroup.map (n := Fin 3) integralEmbedding) ×ˢ matrices)
  have finite_products_compact : IsCompact finiteProducts :=
    (finiteIntegralGL_isCompact.prod matrices_compact).image
      (continuous_fst.mul (finiteGroup_continuous.comp continuous_snd))
  obtain ⟨compactBound, compact_nonnegative, bounded⟩ :=
    normalizedScalarProfile_compact_real_finite_bound flat (normalizedScalarProfile_compact_bound flat) parameters finiteProducts parameters_compact finite_products_compact
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
  refine ⟨uniformBound * compactBound, mul_nonneg (le_max_left _ _) compact_nonnegative, ?_⟩
  intro parameter parameter_in matrix matrix_in flag
  have parameter_nonnegative := nonnegative parameter parameter_in
  have replacement := normalizedScalarProfile_norm_of_representative flat parameter
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
  have finite_member : finiteGroup (representative * matrix) ∈ finiteProducts := by
    rw [map_mul]
    exact ⟨(finiteGroup representative, matrix), ⟨representative_integral, matrix_in⟩, rfl⟩
  have bound_at := bounded parameter parameter_in (representative * matrix) finite_member
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
      Real.log |(realGroup matrix).val.det| -
        (3 / 2 + parameter.re) * Real.log height ≤
      Real.log rowNorm * (-(3 / 2 + parameter.re)) +
        ((inductionExponent .plane parameter).re * Real.log |(realGroup matrix).val.det| +
          (3 / 2 + parameter.re) * Real.log translationBound) := by
    nlinarith [mul_le_mul_of_nonneg_left log_row parameter_nonnegative]
  calc
    _ ≤ Real.exp ((inductionExponent .plane parameter).re *
        Real.log |(realGroup matrix).val.det| -
          (3 / 2 + parameter.re) * Real.log height) * compactBound := bound_at
    _ ≤ Real.exp (Real.log rowNorm * (-(3 / 2 + parameter.re)) +
        ((inductionExponent .plane parameter).re * Real.log |(realGroup matrix).val.det| +
          (3 / 2 + parameter.re) * Real.log translationBound)) * compactBound :=
      mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr exponent_bound) compact_nonnegative
    _ = rowNorm ^ (-(3 / 2 + parameter.re)) * (coefficient (parameter, matrix) * compactBound) := by
      rw [Real.exp_add, ← Real.rpow_def_of_pos row_positive]
      exact mul_assoc _ _ _
    _ ≤ rowNorm ^ (-(3 / 2 + parameter.re)) * (uniformBound * compactBound) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (coefficient_bound parameter parameter_in matrix matrix_in) compact_nonnegative)
        (Real.rpow_nonneg (norm_nonneg _) _)

theorem normalized_scalar_sum_compact_boundary_bound
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (matrices : Set AdelicGL) (compact : IsCompact matrices) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ᶠ displacement : ℝ in nhdsWithin 0 (Set.Ioi 0),
      ∀ matrix ∈ matrices, displacement *
        ‖∑' flag, eisensteinSummand (unitaryNormalize degree family)
          ((3 : ℂ) / 2 + (displacement : ℂ)) matrix flag‖ ≤ bound := by
  let parameters : Set ℂ := (fun displacement : ℝ => (3 : ℂ) / 2 + (displacement : ℂ)) '' Set.Icc 0 1
  have parameters_compact : IsCompact parameters :=
    isCompact_Icc.image (continuous_const.add Complex.continuous_ofReal)
  have nonnegative : ∀ parameter ∈ parameters, 0 ≤ (3 : ℝ) / 2 + parameter.re := by
    rintro parameter ⟨displacement, member, rfl⟩
    norm_num
    linarith [member.1]
  obtain ⟨coefficient, coefficient_nonnegative, estimate⟩ :=
    normalized_scalar_profile_compact_power_bound flat parameters matrices parameters_compact compact nonnegative
  obtain ⟨latticeBound, lattice_nonnegative, lattice_estimate⟩ := planeFlagIntegerRow_boundary_bound
  refine ⟨latticeBound * coefficient, mul_nonneg lattice_nonnegative coefficient_nonnegative, ?_⟩
  have below_one : ∀ᶠ displacement : ℝ in nhdsWithin 0 (Set.Ioi 0), displacement < 1 :=
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, below_one, lattice_estimate]
    with displacement displacement_positive displacement_small lattice_estimate
  change 0 < displacement at displacement_positive
  intro matrix matrix_in
  have parameter_in : (3 : ℂ) / 2 + (displacement : ℂ) ∈ parameters :=
    ⟨displacement, ⟨displacement_positive.le, displacement_small.le⟩, rfl⟩
  have exponent : -((3 : ℝ) / 2 + ((3 : ℂ) / 2 + (displacement : ℂ)).re) = -3 - displacement := by
    norm_num
    ring
  have bound_term (flag : Flags .plane) :
      ‖eisensteinSummand (unitaryNormalize degree family) ((3 : ℂ) / 2 + (displacement : ℂ)) matrix flag‖ ≤
        ‖(fun index => (planeFlagIntegerRow flag index : ℝ))‖ ^ (-3 - displacement) * coefficient := by
    have bound_at := estimate _ parameter_in matrix matrix_in flag
    rw [exponent] at bound_at
    exact (normalized_scalar_norm_le_profile flat _ _).trans bound_at
  have majorant_summable := (planeFlagIntegerRow_summable (-3 - displacement) (by linarith)).mul_right coefficient
  have norm_summable := Summable.of_nonneg_of_le (fun flag => norm_nonneg
    (eisensteinSummand (unitaryNormalize degree family) ((3 : ℂ) / 2 + (displacement : ℂ)) matrix flag))
      bound_term majorant_summable
  have sum_bound := (norm_tsum_le_tsum_norm norm_summable).trans
    (norm_summable.tsum_le_tsum bound_term majorant_summable)
  rw [tsum_mul_right] at sum_bound
  calc
    _ ≤ displacement * ((∑' flag : Flags .plane,
        ‖(fun index => (planeFlagIntegerRow flag index : ℝ))‖ ^ (-3 - displacement)) * coefficient) :=
      mul_le_mul_of_nonneg_left sum_bound displacement_positive.le
    _ = (displacement * (∑' flag : Flags .plane,
        ‖(fun index => (planeFlagIntegerRow flag index : ℝ))‖ ^ (-3 - displacement))) * coefficient := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right lattice_estimate coefficient_nonnegative

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
