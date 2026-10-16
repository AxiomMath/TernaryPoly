module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Scalar.ProfileGrowth
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.SectionScalarBounds

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem normalizedScalarProfile_integral_finite_bound
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ parameter matrix,
      finiteGroup matrix ∈ Set.range (GeneralLinearGroup.map integralEmbedding) →
      ‖normalizedScalarProfile flat parameter matrix‖ ≤
        Real.exp ((inductionExponent .plane parameter).re * Real.log |(realGroup matrix).val.det| -
          (3 / 2 + parameter.re) * Real.log (realPlaneHeight (realGroup matrix))) * bound := by
  obtain ⟨bound, nonnegative, bounded⟩ := normalizedScalarProfile_maximalCompact_bound flat
  refine ⟨bound, nonnegative, ?_⟩
  intro parameter matrix integral
  obtain ⟨compactMatrix, orthogonal, reduction⟩ := normalizedScalarProfile_real_compact_reduction flat matrix
  rw [reduction parameter]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
  exact bounded parameter (combineGL compactMatrix (finiteGroup matrix))
    ⟨by simpa only [realGroup_combineGL] using orthogonal,
      by simpa only [finiteGroup_combineGL] using integral⟩

theorem normalized_scalar_flag_transformed_row_bound
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ parameter : ℂ, -(3 / 2 : ℝ) ≤ parameter.re → ∀ matrix,
      finiteGroup matrix ∈ Set.range (GeneralLinearGroup.map integralEmbedding) → ∀ flag : Flags .plane,
      ‖eisensteinSummand (unitaryNormalize degree family) parameter matrix flag‖ ≤
        |(realGroup matrix).val.det| ^ (inductionExponent .plane parameter).re *
          ‖(fun index => (planeFlagIntegerRow flag index : ℝ)) ᵥ* (realGroup matrix).val‖ ^
            (-(3 / 2 + parameter.re)) * bound := by
  obtain ⟨bound, nonnegative, bounded⟩ := normalizedScalarProfile_integral_finite_bound flat
  refine ⟨bound, nonnegative, ?_⟩
  intro parameter large matrix integral flag
  have scalar_bound := normalized_scalar_norm_le_profile flat parameter (rationalGroup flag.out⁻¹ * matrix)
  have replacement := normalizedScalarProfile_norm_of_representative flat parameter
    (integralRational (planeFlagIntegralMatrix flag)) matrix
  rw [planeFlagIntegralMatrix_spec] at replacement
  rw [replacement] at scalar_bound
  let representative := rationalGroup ((integralRational (planeFlagIntegralMatrix flag))⁻¹)
  have representative_integral : finiteGroup representative ∈ Set.range (GeneralLinearGroup.map integralEmbedding) := by
    simpa only [representative, map_inv] using integral_rational_finite_integral (planeFlagIntegralMatrix flag)⁻¹
  have determinant_norm : |(realGroup (representative * matrix)).val.det| = |(realGroup matrix).val.det| := by
    rw [map_mul]
    change |((realGroup representative).val * (realGroup matrix).val).det| = _
    rw [Matrix.det_mul, abs_mul]
    have representative_det : |(realGroup representative).val.det| = 1 := by
      simpa only [representative, map_inv] using integralRational_real_abs_det (planeFlagIntegralMatrix flag)⁻¹
    rw [representative_det, one_mul]
  have estimate := bounded parameter (representative * matrix) (finite_integral_mul representative_integral integral)
  rw [determinant_norm] at estimate
  let row := (fun index => (planeFlagIntegerRow flag index : ℝ)) ᵥ* (realGroup matrix).val
  have row_eq : row = (realGroup (representative * matrix)).val 2 := by
    dsimp only [row]
    rw [planeFlagIntegerRow_real, map_mul]
    rfl
  have row_positive : 0 < ‖row‖ := by
    apply norm_pos_iff.mpr
    intro zero
    have product := congrArg (fun matrix : Matrix (Fin 3) (Fin 3) ℝ => matrix 2 2)
      (realGroup (representative * matrix)).val_inv
    change (∑ index, (realGroup (representative * matrix)).val 2 index *
      (realGroup (representative * matrix)).inv index 2) = 1 at product
    simp only [← row_eq, zero, Pi.zero_apply, zero_mul, Finset.sum_const_zero] at product
    norm_num at product
  have height_positive := realPlaneHeight_pos (realGroup (representative * matrix))
  have row_le : ‖row‖ ≤ realPlaneHeight (realGroup (representative * matrix)) := by
    rw [row_eq]
    exact real_row_norm_le_height _
  have determinant_positive : 0 < |(realGroup matrix).val.det| := abs_pos.mpr (realGroup matrix).det_ne_zero
  have power_bound : (realPlaneHeight (realGroup (representative * matrix))) ^ (-(3 / 2 + parameter.re)) ≤
      ‖row‖ ^ (-(3 / 2 + parameter.re)) :=
    Real.rpow_le_rpow_of_nonpos row_positive row_le (by linarith)
  calc
    _ ≤ ‖normalizedScalarProfile flat parameter (representative * matrix)‖ := scalar_bound
    _ ≤ _ := estimate
    _ = |(realGroup matrix).val.det| ^ (inductionExponent .plane parameter).re *
        (realPlaneHeight (realGroup (representative * matrix))) ^ (-(3 / 2 + parameter.re)) * bound := by
      rw [Real.rpow_def_of_pos determinant_positive, Real.rpow_def_of_pos height_positive, ← Real.exp_add]
      congr 2
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left power_bound (Real.rpow_nonneg (abs_nonneg _) _)) nonnegative

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
