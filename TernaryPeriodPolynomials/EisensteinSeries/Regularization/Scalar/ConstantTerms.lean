module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Scalar.FlagIntegrability
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.AbsoluteConstantTerms
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Scalar.KernelAnalyticity

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory Filter

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem scalar_flag_radical_norm_integrals_summable
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (parameter : ℂ)
    (large : -(degree : ℝ) / 2 < parameter.re) (matrix : AdelicGL)
    (radical : Adeles × Adeles → AdelicGL) (continuous : Continuous radical) :
    (∀ flag : Flags .plane, Integrable (fun point : Adeles × Adeles =>
      eisensteinSummand family parameter (radical point * matrix) flag) planeDomainMeasure) ∧
    Summable (fun flag : Flags .plane => ∫ point : Adeles × Adeles,
      ‖eisensteinSummand family parameter (radical point * matrix) flag‖ ∂planeDomainMeasure) := by
  let container : Set Adeles := Set.Icc 0 1 ×ˢ Set.range integralEmbedding
  have compact_container : IsCompact container := isCompact_Icc.prod integralLattice_isCompact
  have domain_subset : additiveDomain ⊆ container := by
    intro point member
    exact ⟨⟨member.1.1, member.1.2.le⟩, member.2⟩
  have domain_measurable : MeasurableSet additiveDomain :=
    measurableSet_Ico.prod integralLattice_isCompact.measurableSet
  have contained : ∀ᵐ point ∂planeDomainMeasure, point ∈ container ×ˢ container := by
    rw [planeDomainMeasure_eq]
    filter_upwards [ae_restrict_mem (domain_measurable.prod domain_measurable)] with point member
    exact ⟨domain_subset member.1, domain_subset member.2⟩
  apply scalar_flag_norm_integrals_summable flat parameter large planeDomainMeasure
    (continuous.mul continuous_const)
    ((fun point => radical point * matrix) '' (container ×ˢ container))
    ((compact_container.prod compact_container).image (continuous.mul continuous_const))
  filter_upwards [contained] with point member
  exact ⟨point, member, rfl⟩

theorem scalar_flag_radical_enorm_integrals_ne_top
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (parameter : ℂ)
    (large : -(degree : ℝ) / 2 < parameter.re) (matrix : AdelicGL)
    (radical : Adeles × Adeles → AdelicGL) (continuous : Continuous radical) :
    (∑' flag : Flags .plane, ∫⁻ point : Adeles × Adeles,
      ‖eisensteinSummand family parameter (radical point * matrix) flag‖ₑ ∂planeDomainMeasure) ≠ ⊤ := by
  obtain ⟨integrable, summable⟩ := scalar_flag_radical_norm_integrals_summable
    flat parameter large matrix radical continuous
  simp_rw [← ofReal_integral_norm_eq_lintegral_enorm (integrable _)]
  exact summable.tsum_ofReal_ne_top

theorem scalar_plane_constant_term
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (parameter : ℂ)
    (large : -(degree : ℝ) / 2 < parameter.re) (matrix : AdelicGL) :
    Integrable (fun point : Adeles × Adeles => ∑' flag,
      eisensteinSummand family parameter (planeUnipotent point.1 point.2 * matrix) flag) planeDomainMeasure ∧
    (∫ point : Adeles × Adeles, ∑' flag,
      eisensteinSummand family parameter (planeUnipotent point.1 point.2 * matrix) flag
        ∂planeDomainMeasure) = family parameter matrix := by
  apply plane_constant_term_of_absolute_integrability (flat.1 parameter) matrix
    (scalar_flag_radical_enorm_integrals_ne_top flat parameter large matrix
      (fun point => planeUnipotent point.1 point.2) planeUnipotent_continuous)
  intro point
  exact (scalar_flag_summable flat parameter large _).hasSum

theorem scalar_standard_integrable
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (parameter : ℂ)
    (large : -(degree : ℝ) / 2 < parameter.re) (matrix : AdelicGL) :
    Integrable (standardIntegrand family parameter matrix) radicalMeasure := by
  refine ⟨(standardIntegrand_continuous (flat.1 parameter) matrix).aestronglyMeasurable, ?_⟩
  exact lt_of_le_of_lt (standard_norm_le_line_summands (flat.1 parameter) matrix)
    (scalar_flag_radical_enorm_integrals_ne_top flat parameter large matrix
      (fun point => lineUnipotent point.1 point.2) lineUnipotent_continuous).lt_top

theorem scalar_associate_constant_term
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (parameter : ℂ)
    (large : -(degree : ℝ) / 2 < parameter.re) (matrix : AdelicGL) :
    Integrable (fun point : Adeles × Adeles => ∑' flag,
      eisensteinSummand family parameter (lineUnipotent point.1 point.2 * matrix) flag) planeDomainMeasure ∧
    (∫ point : Adeles × Adeles, ∑' flag,
      eisensteinSummand family parameter (lineUnipotent point.1 point.2 * matrix) flag
        ∂planeDomainMeasure) =
      ∫ point, standardIntegrand family parameter matrix point ∂radicalMeasure := by
  apply associate_constant_term_of_absolute_integrability (flat.1 parameter) matrix
    (scalar_flag_radical_enorm_integrals_ne_top flat parameter large matrix
      (fun point => lineUnipotent point.1 point.2) lineUnipotent_continuous)
  intro point
  exact (scalar_flag_summable flat parameter large _).hasSum

theorem scalar_standard_integral_analytic
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (matrix : AdelicGL) :
    AnalyticOnNhd ℂ (fun parameter => ∫ point, standardIntegrand family parameter matrix point ∂radicalMeasure)
      {parameter : ℂ | -(degree : ℝ) / 2 < parameter.re} :=
  standard_integral_analytic_right flat matrix (-(degree : ℝ) / 2)
    (fun parameter large => scalar_standard_integrable flat parameter large matrix)

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
