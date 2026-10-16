module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.GlobalFlagNormBounds
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Radical.Continuity

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory Filter

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem normalized_flag_norm_integrals_summable_all
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (parameter : ℂ) (large : 3 / 2 < parameter.re)
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] [SecondCountableTopology X]
    (measure : Measure X) [IsFiniteMeasure measure] {map : X → AdelicGL} (continuous : Continuous map)
    (matrices : Set AdelicGL) (compact : IsCompact matrices)
    (contained : ∀ᵐ point ∂measure, map point ∈ matrices) :
    (∀ flag : Flags .plane, Integrable
      (fun point => (normalizedCuspVector flat.1 parameter (rationalGroup flag.out⁻¹ * map point)).val) measure) ∧
    Summable (fun flag : Flags .plane => ∫ point,
      ‖(normalizedCuspVector flat.1 parameter (rationalGroup flag.out⁻¹ * map point)).val‖ ∂measure) := by
  obtain ⟨majorant, summable, bounded⟩ := normalized_flag_compact_summable_majorant_all flat
    {parameter} matrices isCompact_singleton compact (by simpa)
  have vector_continuous (flag : Flags .plane) := (normalizedCuspVector_continuous flat.1 parameter).comp
    ((continuous_const (y := rationalGroup flag.out⁻¹)).mul continuous)
  have bound_ae (flag : Flags .plane) : ∀ᵐ point ∂measure,
      ‖(normalizedCuspVector flat.1 parameter (rationalGroup flag.out⁻¹ * map point)).val‖ ≤ majorant flag := by
    filter_upwards [contained] with point member
    exact bounded parameter rfl (map point) member flag
  have integrable (flag : Flags .plane) : Integrable
      (fun point => (normalizedCuspVector flat.1 parameter (rationalGroup flag.out⁻¹ * map point)).val) measure :=
    Integrable.of_bound (vector_continuous flag).stronglyMeasurable.aestronglyMeasurable _ (bound_ae flag)
  refine ⟨integrable, ?_⟩
  apply (summable.mul_left (measure.real Set.univ)).of_nonneg_of_le
    (fun _ => integral_nonneg (fun _ => norm_nonneg _))
  intro flag
  have integral_bound := integral_mono_ae (integrable flag).norm (integrable_const (majorant flag)) (bound_ae flag)
  simpa only [integral_const, smul_eq_mul] using integral_bound

theorem normalized_flag_radical_norm_integrals_summable_all
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (parameter : ℂ) (large : 3 / 2 < parameter.re)
    (matrix : AdelicGL)
    (radical : Adeles × Adeles → AdelicGL) (continuous : Continuous radical) :
    (∀ flag : Flags .plane, Integrable (fun point : Adeles × Adeles =>
      (normalizedCuspVector flat.1 parameter (rationalGroup flag.out⁻¹ * (radical point * matrix))).val)
        planeDomainMeasure) ∧
    Summable (fun flag : Flags .plane => ∫ point : Adeles × Adeles,
      ‖(normalizedCuspVector flat.1 parameter (rationalGroup flag.out⁻¹ * (radical point * matrix))).val‖
        ∂planeDomainMeasure) := by
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
  apply normalized_flag_norm_integrals_summable_all flat parameter large planeDomainMeasure
    (continuous.mul continuous_const)
    ((fun point => radical point * matrix) '' (container ×ˢ container))
    ((compact_container.prod compact_container).image (continuous.mul continuous_const))
  filter_upwards [contained] with point member
  exact ⟨point, member, rfl⟩

theorem normalized_flag_plane_norm_integrals_summable_all
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (parameter : ℂ) (large : 3 / 2 < parameter.re)
    (matrix : AdelicGL) :
    Summable (fun flag : Flags .plane => ∫ point : Adeles × Adeles,
      ‖(normalizedCuspVector flat.1 parameter
        (rationalGroup flag.out⁻¹ * (planeUnipotent point.1 point.2 * matrix))).val‖ ∂planeDomainMeasure) :=
  (normalized_flag_radical_norm_integrals_summable_all flat parameter large matrix
    (fun point => planeUnipotent point.1 point.2) planeUnipotent_continuous).2

theorem normalized_flag_line_norm_integrals_summable_all
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (parameter : ℂ) (large : 3 / 2 < parameter.re)
    (matrix : AdelicGL) :
    Summable (fun flag : Flags .plane => ∫ point : Adeles × Adeles,
      ‖(normalizedCuspVector flat.1 parameter
        (rationalGroup flag.out⁻¹ * (lineUnipotent point.1 point.2 * matrix))).val‖ ∂planeDomainMeasure) :=
  (normalized_flag_radical_norm_integrals_summable_all flat parameter large matrix
    (fun point => lineUnipotent point.1 point.2) lineUnipotent_continuous).2

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
