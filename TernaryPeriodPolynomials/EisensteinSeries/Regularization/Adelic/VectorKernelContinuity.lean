module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Adelic.VectorKernelIntegrability
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.Normed.Group.FunctionSeries

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory Filter

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

instance adelicGL_firstCountable : FirstCountableTopology AdelicGL := by
  let : FirstCountableTopology (Matrix (Fin 3) (Fin 3) Adeles) :=
    inferInstanceAs (FirstCountableTopology (Fin 3 → Fin 3 → Adeles))
  let : FirstCountableTopology (Matrix (Fin 3) (Fin 3) Adeles)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isInducing.firstCountableTopology
  exact (Units.isClosedEmbedding_embedProduct (α := Matrix (Fin 3) (Fin 3) Adeles)).isEmbedding.isInducing.firstCountableTopology

instance adelicGL_locallyCompact : LocallyCompactSpace AdelicGL := by
  let : LocallyCompactSpace (Matrix (Fin 3) (Fin 3) Adeles) :=
    inferInstanceAs (LocallyCompactSpace (Fin 3 → Fin 3 → Adeles))
  let : LocallyCompactSpace (Matrix (Fin 3) (Fin 3) Adeles)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  exact (Units.isClosedEmbedding_embedProduct (α := Matrix (Fin 3) (Fin 3) Adeles)).locallyCompactSpace

theorem radicalDomain_compact_carrier :
    ∃ domain : Set (Adeles × Adeles), IsCompact domain ∧
      ∀ᵐ point ∂planeDomainMeasure, point ∈ domain := by
  let container : Set Adeles := Set.Icc 0 1 ×ˢ Set.range integralEmbedding
  have compact_container : IsCompact container := isCompact_Icc.prod integralLattice_isCompact
  have domain_subset : additiveDomain ⊆ container := by
    intro point member
    exact ⟨⟨member.1.1, member.1.2.le⟩, member.2⟩
  have domain_measurable : MeasurableSet additiveDomain :=
    measurableSet_Ico.prod integralLattice_isCompact.measurableSet
  refine ⟨container ×ˢ container, compact_container.prod compact_container, ?_⟩
  rw [planeDomainMeasure_eq]
  filter_upwards [ae_restrict_mem (domain_measurable.prod domain_measurable)] with point member
  exact ⟨domain_subset member.1, domain_subset member.2⟩

theorem continuous_integral_of_compact_carrier
    {X Y E : Type*} [TopologicalSpace X] [FirstCountableTopology X] [LocallyCompactSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [SecondCountableTopologyEither Y E]
    (measure : Measure Y) [IsLocallyFiniteMeasure measure]
    (family : X → Y → E) (continuous : Continuous (Function.uncurry family))
    (domain : Set Y) (compact : IsCompact domain) (contained : ∀ᵐ point ∂measure, point ∈ domain) :
    Continuous (fun parameter => ∫ point, family parameter point ∂measure) := by
  have result := continuous_parametric_integral_of_continuous (μ := measure) continuous compact
  simpa only [Measure.restrict_eq_self_of_ae_mem contained] using result

theorem normalized_standard_vector_rational_integral_continuous
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (rational : ℚ × ℚ) :
    Continuous (fun input : ℂ × AdelicGL => ∫ coordinates : Adeles × Adeles,
      (normalizedCuspVector flat.1 input.1
        (weyl⁻¹ * lineUnipotent (coordinates.1 - rationalAdele rational.1)
          (coordinates.2 - rationalAdele rational.2) * input.2)).val ∂planeDomainMeasure) := by
  obtain ⟨domain, compact, contained⟩ := radicalDomain_compact_carrier
  apply continuous_integral_of_compact_carrier planeDomainMeasure _ _ domain compact contained
  have translated : Continuous (fun coordinates : Adeles × Adeles =>
      lineUnipotent (coordinates.1 - rationalAdele rational.1)
        (coordinates.2 - rationalAdele rational.2)) :=
    lineUnipotent_continuous.comp
      ((continuous_fst.sub continuous_const).prodMk (continuous_snd.sub continuous_const))
  have joint := (normalizedCuspVector_joint_continuous flat).comp
    ((continuous_fst.comp continuous_fst).prodMk
      (((continuous_const (y := weyl⁻¹)).mul (translated.comp continuous_snd)).mul
        (continuous_snd.comp continuous_fst)))
  dsimp only [Function.comp_def, Function.uncurry] at joint ⊢
  exact joint

theorem normalized_standard_vector_rational_majorant
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family)
    (parameters : Set ℂ) (matrices : Set AdelicGL)
    (parameters_compact : IsCompact parameters) (matrices_compact : IsCompact matrices)
    (large : ∀ parameter ∈ parameters, 3 / 2 < parameter.re) :
    ∃ majorant : ℚ × ℚ → ℝ, Summable majorant ∧
      ∀ parameter ∈ parameters, ∀ matrix ∈ matrices,
        ∀ᵐ coordinates : Adeles × Adeles ∂planeDomainMeasure, ∀ rational : ℚ × ℚ,
          ‖(normalizedCuspVector flat.1 parameter
            (weyl⁻¹ * lineUnipotent (coordinates.1 - rationalAdele rational.1)
              (coordinates.2 - rationalAdele rational.2) * matrix)).val‖ ≤ majorant rational := by
  obtain ⟨domain, compact, contained⟩ := radicalDomain_compact_carrier
  have product_continuous : Continuous (fun input : (Adeles × Adeles) × AdelicGL =>
      lineUnipotent input.1.1 input.1.2 * input.2) :=
    (lineUnipotent_continuous.comp continuous_fst).mul continuous_snd
  obtain ⟨majorant, summable, bounded⟩ := normalized_flag_compact_summable_majorant_all flat parameters
    ((fun input : (Adeles × Adeles) × AdelicGL => lineUnipotent input.1.1 input.1.2 * input.2) ''
      (domain ×ˢ matrices)) parameters_compact ((compact.prod matrices_compact).image product_continuous) large
  refine ⟨fun rational => majorant (associateFlag (.inr rational)),
    summable.comp_injective (associateFlag_injective.comp Sum.inr_injective), ?_⟩
  intro parameter parameter_in matrix matrix_in
  filter_upwards [contained] with coordinates coordinates_in
  intro rational
  rw [← normalized_vector_associate_open_norm flat.1]
  exact bounded parameter parameter_in (lineUnipotent coordinates.1 coordinates.2 * matrix)
    ⟨(coordinates, matrix), ⟨coordinates_in, matrix_in⟩, rfl⟩ (associateFlag (.inr rational))

theorem normalized_standard_vector_rational_integrals_majorant
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family)
    (parameters : Set ℂ) (matrices : Set AdelicGL)
    (parameters_compact : IsCompact parameters) (matrices_compact : IsCompact matrices)
    (large : ∀ parameter ∈ parameters, 3 / 2 < parameter.re) :
    ∃ majorant : ℚ × ℚ → ℝ, Summable majorant ∧
      ∀ rational : ℚ × ℚ, ∀ input ∈ parameters ×ˢ matrices,
        ‖∫ coordinates : Adeles × Adeles,
          (normalizedCuspVector flat.1 input.1
            (weyl⁻¹ * lineUnipotent (coordinates.1 - rationalAdele rational.1)
              (coordinates.2 - rationalAdele rational.2) * input.2)).val ∂planeDomainMeasure‖ ≤
        majorant rational := by
  obtain ⟨majorant, summable, bounded⟩ := normalized_standard_vector_rational_majorant
    flat parameters matrices parameters_compact matrices_compact large
  refine ⟨majorant, summable, ?_⟩
  intro rational input member
  have bound_ae := (bounded input.1 member.1 input.2 member.2).mono (fun _ bound => bound rational)
  simpa using norm_integral_le_of_norm_le_const bound_ae

theorem normalized_standard_vector_integral_continuousOn_compact
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family)
    (parameters : Set ℂ) (matrices : Set AdelicGL)
    (parameters_compact : IsCompact parameters) (matrices_compact : IsCompact matrices)
    (large : ∀ parameter ∈ parameters, 3 / 2 < parameter.re) :
    ContinuousOn (fun input : ℂ × AdelicGL => ∫ point : Adeles × Adeles,
      (normalizedCuspVector flat.1 input.1 (weyl⁻¹ * lineUnipotent point.1 point.2 * input.2)).val
        ∂radicalMeasure) (parameters ×ˢ matrices) := by
  obtain ⟨majorant, summable, bounded⟩ := normalized_standard_vector_rational_integrals_majorant
    flat parameters matrices parameters_compact matrices_compact large
  have continuous := continuousOn_tsum
    (fun rational => (normalized_standard_vector_rational_integral_continuous flat rational).continuousOn)
    summable bounded
  apply continuous.congr
  intro input member
  exact radical_integral_eq_rational_tsum _
    (normalized_standard_vector_integrable flat input.1 (large input.1 member.1) input.2)

theorem normalized_standard_vector_integral_joint_continuous
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) :
    ContinuousOn (fun input : ℂ × AdelicGL => ∫ point : Adeles × Adeles,
      (normalizedCuspVector flat.1 input.1 (weyl⁻¹ * lineUnipotent point.1 point.2 * input.2)).val
        ∂radicalMeasure) {input | 3 / 2 < input.1.re} := by
  apply continuousOn_of_forall_continuousAt
  intro input large
  obtain ⟨parameters, parameters_compact, parameter_interior, parameters_subset⟩ :=
    exists_compact_subset (isOpen_lt continuous_const Complex.continuous_re) large
  obtain ⟨matrices, matrices_compact, matrices_nhds⟩ :=
    WeaklyLocallyCompactSpace.exists_compact_mem_nhds input.2
  apply (normalized_standard_vector_integral_continuousOn_compact flat parameters matrices
    parameters_compact matrices_compact parameters_subset).continuousAt
  rw [nhds_prod_eq]
  exact Filter.prod_mem_prod (mem_interior_iff_mem_nhds.mp parameter_interior) matrices_nhds

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
