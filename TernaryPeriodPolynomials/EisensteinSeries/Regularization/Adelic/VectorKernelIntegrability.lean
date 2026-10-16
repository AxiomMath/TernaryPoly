module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.GlobalFlagVectorIntegrability
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.AssociateOpenOrbit
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.StandardIntegralTruncations

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory Filter

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem normalized_vector_associate_open_norm
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (induced : ∀ parameter, IsInduced inducingData .plane parameter (family parameter))
    (parameter : ℂ) (rational : ℚ × ℚ) (coordinates : Adeles × Adeles) (matrix : AdelicGL) :
    ‖(normalizedCuspVector induced parameter
      (rationalGroup (associateFlag (.inr rational)).out⁻¹ *
        (lineUnipotent coordinates.1 coordinates.2 * matrix))).val‖ =
    ‖(normalizedCuspVector induced parameter
      (weyl⁻¹ * lineUnipotent (coordinates.1 - rationalAdele rational.1)
        (coordinates.2 - rationalAdele rational.2) * matrix)).val‖ := by
  rw [associateFlag, associateFlagMatrix, normalizedCuspVector_norm_of_representative,
    ← mul_assoc, associate_open_unipotent_identity]

theorem normalized_vector_standard_norm_le_line_summands
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (induced : ∀ parameter, IsInduced inducingData .plane parameter (family parameter))
    (parameter : ℂ) (matrix : AdelicGL) :
    (∫⁻ coordinates : Adeles × Adeles,
      ‖(normalizedCuspVector induced parameter
        (weyl⁻¹ * lineUnipotent coordinates.1 coordinates.2 * matrix)).val‖ₑ ∂radicalMeasure) ≤
    ∑' flag : Flags .plane, ∫⁻ coordinates : Adeles × Adeles,
      ‖(normalizedCuspVector induced parameter
        (rationalGroup flag.out⁻¹ * (lineUnipotent coordinates.1 coordinates.2 * matrix))).val‖ₑ
          ∂planeDomainMeasure := by
  rw [radical_lintegral_eq_rational_tsum]
  simp_rw [← ofReal_norm, ← normalized_vector_associate_open_norm induced]
  exact le_trans (le_of_eq (by rfl)) <| ENNReal.tsum_comp_le_tsum_of_injective
    (associateFlag_injective.comp Sum.inr_injective) _

theorem normalized_flag_radical_enorm_integrals_ne_top
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (parameter : ℂ) (large : 3 / 2 < parameter.re)
    (matrix : AdelicGL) (radical : Adeles × Adeles → AdelicGL) (continuous : Continuous radical) :
    (∑' flag : Flags .plane, ∫⁻ coordinates : Adeles × Adeles,
      ‖(normalizedCuspVector flat.1 parameter
        (rationalGroup flag.out⁻¹ * (radical coordinates * matrix))).val‖ₑ ∂planeDomainMeasure) ≠ ⊤ := by
  obtain ⟨integrable, summable⟩ := normalized_flag_radical_norm_integrals_summable_all
    flat parameter large matrix radical continuous
  simp_rw [← ofReal_integral_norm_eq_lintegral_enorm (integrable _)]
  exact summable.tsum_ofReal_ne_top

theorem normalized_standard_vector_integrable
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (parameter : ℂ) (large : 3 / 2 < parameter.re)
    (matrix : AdelicGL) :
    Integrable (fun coordinates : Adeles × Adeles =>
      (normalizedCuspVector flat.1 parameter
        (weyl⁻¹ * lineUnipotent coordinates.1 coordinates.2 * matrix)).val) radicalMeasure := by
  have continuous := (normalizedCuspVector_continuous flat.1 parameter).comp
    (((continuous_const (y := weyl⁻¹)).mul lineUnipotent_continuous).mul (continuous_const (y := matrix)))
  refine ⟨continuous.stronglyMeasurable.aestronglyMeasurable, ?_⟩
  exact lt_of_le_of_lt (normalized_vector_standard_norm_le_line_summands flat.1 parameter matrix)
    (normalized_flag_radical_enorm_integrals_ne_top flat parameter large matrix
      (fun coordinates => lineUnipotent coordinates.1 coordinates.2) lineUnipotent_continuous).lt_top

theorem normalized_standard_vector_integral_analytic
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (matrix : AdelicGL) :
    AnalyticOnNhd ℂ (fun nearby => ∫ point : Adeles × Adeles,
      (normalizedCuspVector flat.1 nearby (weyl⁻¹ * lineUnipotent point.1 point.2 * matrix)).val
        ∂radicalMeasure) {parameter : ℂ | 3 / 2 < parameter.re} :=
  normalized_standard_vector_integral_analytic_right flat matrix (3 / 2)
    (fun parameter large => normalized_standard_vector_integrable flat parameter large matrix)

theorem normalized_standard_vector_truncations_locally_uniform
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (matrix : AdelicGL) :
    TendstoLocallyUniformlyOn
      (fun index parameter => ∫ point in radicalCompactExhaustion index,
        (normalizedCuspVector flat.1 parameter (weyl⁻¹ * lineUnipotent point.1 point.2 * matrix)).val
          ∂radicalMeasure)
      (fun parameter => ∫ point : Adeles × Adeles,
        (normalizedCuspVector flat.1 parameter (weyl⁻¹ * lineUnipotent point.1 point.2 * matrix)).val
          ∂radicalMeasure) atTop {parameter : ℂ | 3 / 2 < parameter.re} :=
  normalized_standard_vector_truncations_locally_uniform_right flat matrix (3 / 2)
    (fun parameter large => normalized_standard_vector_integrable flat parameter large matrix)

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
