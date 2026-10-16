module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Scalar.ProfileNormContinuity

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

theorem cuspBoundedRealization_translate_difference_norm (cusp : CuspidalRepresentation)
    (first second : cusp.smooth) (matrix : BinaryAdelicGL) :
    ‖cuspBoundedRealization cusp ⟨cusp.π matrix first.val, cusp.smooth_stable matrix _ first.property⟩ -
      cuspBoundedRealization cusp ⟨cusp.π matrix second.val, cusp.smooth_stable matrix _ second.property⟩‖ =
      ‖cuspBoundedRealization cusp first - cuspBoundedRealization cusp second‖ := by
  rw [← map_sub, ← map_sub]
  have equality : (⟨cusp.π matrix first.val, cusp.smooth_stable matrix _ first.property⟩ : cusp.smooth) -
      ⟨cusp.π matrix second.val, cusp.smooth_stable matrix _ second.property⟩ =
      ⟨cusp.π matrix (first - second).val, cusp.smooth_stable matrix _ (first - second).property⟩ := by
    apply Subtype.ext
    exact (map_sub (cusp.π matrix) first.val second.val).symm
  rw [equality, cuspBoundedRealization_translate_norm]

noncomputable def normalizedScalarDifferenceProfile
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (shift : AdelicGL) (parameter : ℂ) (matrix : AdelicGL) :
    BoundedContinuousFunction BinaryAdelicGL ℂ :=
  normalizedScalarProfile flat parameter (matrix * shift) - normalizedScalarProfile flat parameter matrix

theorem normalized_scalar_difference_norm_le_profile
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (shift : AdelicGL) (parameter : ℂ) (matrix : AdelicGL) :
    ‖unitaryNormalize degree family parameter (matrix * shift) - unitaryNormalize degree family parameter matrix‖ ≤
      ‖normalizedScalarDifferenceProfile flat shift parameter matrix‖ := by
  have estimate := BoundedContinuousFunction.norm_coe_le_norm (normalizedScalarDifferenceProfile flat shift parameter matrix) 1
  simpa only [normalizedScalarDifferenceProfile, BoundedContinuousFunction.sub_apply,
    normalizedScalarProfile, cuspBoundedRealization_apply, normalizedCuspVector_at_one] using estimate

theorem normalizedScalarDifferenceProfile_binary_norm
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (shift : AdelicGL) (parameter : ℂ)
    (matrix : AdelicGL) (binary : BinaryAdelicGL) :
    ‖normalizedScalarDifferenceProfile flat shift parameter (planeLevi binary 1 * matrix)‖ =
      Real.exp ((inductionExponent .plane parameter).re * Real.log (adeleNorm (GeneralLinearGroup.det binary) : ℝ)) *
        ‖normalizedScalarDifferenceProfile flat shift parameter matrix‖ := by
  simp only [normalizedScalarDifferenceProfile, normalizedScalarProfile, mul_assoc, normalizedCuspVector_binary,
    map_smul, ← smul_sub, norm_smul, cuspBoundedRealization_translate_difference_norm, normPower_norm]

theorem normalizedScalarDifferenceProfile_rankOne_norm
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (shift : AdelicGL) (parameter : ℂ)
    (matrix : AdelicGL) (scalar : Adelesˣ) :
    ‖normalizedScalarDifferenceProfile flat shift parameter (planeLevi 1 scalar * matrix)‖ =
      Real.exp ((-2 * inductionExponent .plane parameter).re * Real.log (adeleNorm scalar : ℝ)) *
        ‖normalizedScalarDifferenceProfile flat shift parameter matrix‖ := by
  simp only [normalizedScalarDifferenceProfile, normalizedScalarProfile, mul_assoc, normalizedCuspVector_rankOne,
    map_smul, ← smul_sub, norm_smul, norm_mul, inducingData.chi.unitary, one_mul, normPower_norm]

theorem normalizedScalarDifferenceProfile_unipotent
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (shift : AdelicGL) (parameter : ℂ)
    (matrix : AdelicGL) (first second : Adeles) :
    normalizedScalarDifferenceProfile flat shift parameter (planeUnipotent first second * matrix) =
      normalizedScalarDifferenceProfile flat shift parameter matrix := by
  simp only [normalizedScalarDifferenceProfile, mul_assoc, normalizedScalarProfile_unipotent]

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
