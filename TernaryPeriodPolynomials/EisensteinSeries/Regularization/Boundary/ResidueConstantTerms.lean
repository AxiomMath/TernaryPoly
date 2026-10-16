module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Boundary.ResidueIntegrals
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Normalized.ScalarConstantTerms

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory Filter

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

theorem radical_compact_container (radical : Adeles × Adeles → AdelicGL) (continuous : Continuous radical)
    (matrix : AdelicGL) :
    ∃ matrices : Set AdelicGL, IsCompact matrices ∧
      ∀ᵐ point ∂planeDomainMeasure, radical point * matrix ∈ matrices := by
  let container : Set Adeles := Set.Icc 0 1 ×ˢ Set.range integralEmbedding
  have compact_container : IsCompact container := isCompact_Icc.prod integralLattice_isCompact
  have domain_subset : additiveDomain ⊆ container := by
    intro point member
    exact ⟨⟨member.1.1, member.1.2.le⟩, member.2⟩
  have domain_measurable : MeasurableSet additiveDomain :=
    measurableSet_Ico.prod integralLattice_isCompact.measurableSet
  refine ⟨(fun point => radical point * matrix) '' (container ×ˢ container),
    (compact_container.prod compact_container).image (continuous.mul continuous_const), ?_⟩
  rw [planeDomainMeasure_eq]
  filter_upwards [ae_restrict_mem (domain_measurable.prod domain_measurable)] with point member
  exact ⟨point, ⟨domain_subset member.1, domain_subset member.2⟩, rfl⟩

theorem normalizedBoundaryResidue_radical_integrable
    {degree : ℕ} {inducingData : InducingData degree} {family continuation : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family)
    (continuation_spec : IsEisensteinContinuation family continuation)
    (radical : Adeles × Adeles → AdelicGL) (continuous : Continuous radical) (matrix : AdelicGL) :
    Integrable (fun point => normalizedBoundaryResidue degree continuation (radical point * matrix)) planeDomainMeasure := by
  obtain ⟨matrices, compact, contained⟩ := radical_compact_container radical continuous matrix
  exact normalizedBoundaryResidue_integrable flat continuation_spec planeDomainMeasure
    (continuous.mul continuous_const) matrices compact contained

theorem normalizedBoundaryResidue_radical_integral_tendsto
    {degree : ℕ} {inducingData : InducingData degree} {family continuation : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family)
    (continuation_spec : IsEisensteinContinuation family continuation)
    (radical : Adeles × Adeles → AdelicGL) (continuous : Continuous radical) (matrix : AdelicGL) :
    Tendsto (fun displacement : ℝ => (displacement : ℂ) * ∫ point : Adeles × Adeles,
      ∑' flag, eisensteinSummand (unitaryNormalize degree family)
        ((3 : ℂ) / 2 + (displacement : ℂ)) (radical point * matrix) flag ∂planeDomainMeasure)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (∫ point, normalizedBoundaryResidue degree continuation (radical point * matrix) ∂planeDomainMeasure)) := by
  obtain ⟨matrices, compact, contained⟩ := radical_compact_container radical continuous matrix
  simpa only [integral_const_mul, Pi.mul_apply] using normalizedBoundaryResidue_integral_tendsto flat continuation_spec planeDomainMeasure
    (continuous.mul continuous_const) matrices compact contained

theorem normalizedBoundaryResidue_plane_constant_term_zero
    {degree : ℕ} {inducingData : InducingData degree} {family continuation : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family)
    (continuation_spec : IsEisensteinContinuation family continuation) (matrix : AdelicGL) :
    (∫ point : Adeles × Adeles, normalizedBoundaryResidue degree continuation
      (planeUnipotent point.1 point.2 * matrix) ∂planeDomainMeasure) = 0 := by
  have integral_limit := normalizedBoundaryResidue_radical_integral_tendsto flat continuation_spec
    (fun point => planeUnipotent point.1 point.2) planeUnipotent_continuous matrix
  have section_continuous := (unitaryNormalize_analytic degree flat.2.1 matrix ((3 : ℂ) / 2)).continuousAt
  have section_limit := section_continuous.tendsto.comp
    ((positive_real_ray_tendsto ((3 : ℂ) / 2)).mono_right nhdsWithin_le_nhds)
  have scalar_limit : Tendsto (fun displacement : ℝ => (displacement : ℂ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have zero_limit := scalar_limit.mul section_limit
  simp only [zero_mul, Function.comp_def] at zero_limit
  apply tendsto_nhds_unique integral_limit
  apply zero_limit.congr'
  filter_upwards [self_mem_nhdsWithin] with displacement positive
  have large : 3 / 2 < ((3 : ℂ) / 2 + (displacement : ℂ)).re := by norm_num; exact positive
  rw [(normalized_scalar_plane_constant_term flat _ large matrix).2]

theorem normalizedBoundaryResidue_associate_constant_term_limit
    {degree : ℕ} {inducingData : InducingData degree} {family continuation : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family)
    (continuation_spec : IsEisensteinContinuation family continuation) (matrix : AdelicGL) :
    Tendsto (fun displacement : ℝ => (displacement : ℂ) *
      ∫ point, standardIntegrand (unitaryNormalize degree family)
        ((3 : ℂ) / 2 + (displacement : ℂ)) matrix point ∂radicalMeasure)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (∫ point : Adeles × Adeles, normalizedBoundaryResidue degree continuation
        (lineUnipotent point.1 point.2 * matrix) ∂planeDomainMeasure)) := by
  apply (normalizedBoundaryResidue_radical_integral_tendsto flat continuation_spec
    (fun point => lineUnipotent point.1 point.2) lineUnipotent_continuous matrix).congr'
  filter_upwards [self_mem_nhdsWithin] with displacement positive
  have large : 3 / 2 < ((3 : ℂ) / 2 + (displacement : ℂ)).re := by norm_num; exact positive
  rw [(normalized_scalar_associate_constant_term flat _ large matrix).2]

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
