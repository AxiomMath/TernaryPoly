module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.ExponentialIntegrals

@[expose] public section


open MeasureTheory Filter

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem integrable_complement_integral_tendsto_zero
    {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (measure : Measure X) {function : X → E} (integrable : Integrable function measure)
    (domains : ℕ → Set X) (measurable : ∀ index, MeasurableSet (domains index))
    (increasing : Monotone domains) (exhaustive : ∀ point, ∃ index, point ∈ domains index) :
    Tendsto (fun index => ∫ point in (domains index)ᶜ, function point ∂measure) atTop (nhds 0) := by
  have convergence := tendsto_integral_of_dominated_convergence
    (fun point => ‖function point‖)
    (F := fun index => (domains index)ᶜ.indicator function) (f := fun _ => 0)
    (fun index => integrable.aestronglyMeasurable.indicator (measurable index).compl)
    integrable.norm (fun _ => Eventually.of_forall (norm_indicator_le_norm_self function))
    (Eventually.of_forall (fun point => by
      obtain ⟨index, member⟩ := exhaustive point
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop index] with nearby later
      have later_member := increasing later member
      simp only [Set.indicator_of_notMem
        (show point ∉ (domains nearby)ᶜ by simpa only [Set.mem_compl_iff, not_not] using later_member)]))
  simpa only [integral_indicator (measurable _).compl, integral_zero] using convergence

theorem integral_truncation_error_le
    {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (measure : Measure X) {function : X → E} (integrable : Integrable function measure)
    {bound : X → ℝ} (bound_integrable : Integrable bound measure)
    (bounded : ∀ point, ‖function point‖ ≤ bound point)
    {domain : Set X} (measurable : MeasurableSet domain) :
    ‖(∫ point, function point ∂measure) - (∫ point in domain, function point ∂measure)‖ ≤
      ∫ point in domainᶜ, bound point ∂measure := by
  have decomposition := integral_add_compl measurable integrable
  rw [← decomposition, add_sub_cancel_left]
  apply (norm_integral_le_integral_norm _).trans
  exact integral_mono_ae integrable.norm.integrableOn bound_integrable.integrableOn
    (Eventually.of_forall bounded)

theorem integral_truncations_tendstoUniformlyOn_of_bound
    {X E P : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (measure : Measure X) {family : P → X → E} {parameters : Set P}
    (integrable : ∀ parameter ∈ parameters, Integrable (family parameter) measure)
    {bound : X → ℝ} (bound_integrable : Integrable bound measure)
    (bounded : ∀ parameter ∈ parameters, ∀ point, ‖family parameter point‖ ≤ bound point)
    (domains : ℕ → Set X) (measurable : ∀ index, MeasurableSet (domains index))
    (increasing : Monotone domains) (exhaustive : ∀ point, ∃ index, point ∈ domains index) :
    TendstoUniformlyOn (fun index parameter => ∫ point in domains index, family parameter point ∂measure)
      (fun parameter => ∫ point, family parameter point ∂measure) atTop parameters := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro epsilon positive
  have tail := integrable_complement_integral_tendsto_zero measure bound_integrable
    domains measurable increasing exhaustive
  filter_upwards [tail.eventually (gt_mem_nhds positive)] with index small
  intro parameter member
  rw [dist_eq_norm]
  exact (integral_truncation_error_le measure (integrable parameter member) bound_integrable
    (bounded parameter member) (measurable index)).trans_lt small

theorem exponential_integral_truncations_uniform_strip
    {X E : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
    [SecondCountableTopologyEither X E]
    {family : ℂ → X → E}
    (continuous : Continuous (fun input : ℂ × X => family input.1 input.2))
    (exponential : ∀ point, ∃ weight : ℝ, ∀ parameter,
      family parameter point = Complex.exp (parameter * (weight : ℂ)) • family 0 point)
    (measure : Measure X) (lower upper : ℂ)
    (lower_integrable : Integrable (family lower) measure)
    (upper_integrable : Integrable (family upper) measure)
    (domains : ℕ → Set X) (measurable : ∀ index, MeasurableSet (domains index))
    (increasing : Monotone domains) (exhaustive : ∀ point, ∃ index, point ∈ domains index) :
    TendstoUniformlyOn (fun index parameter => ∫ point in domains index, family parameter point ∂measure)
      (fun parameter => ∫ point, family parameter point ∂measure) atTop
      {parameter : ℂ | lower.re ≤ parameter.re ∧ parameter.re ≤ upper.re} := by
  apply integral_truncations_tendstoUniformlyOn_of_bound measure
    (fun parameter member => exponential_family_integrable continuous exponential measure
      lower upper parameter lower_integrable upper_integrable member.1 member.2)
    (lower_integrable.norm.add upper_integrable.norm) _ domains measurable increasing exhaustive
  intro parameter member point
  simp only [Pi.add_apply]
  obtain ⟨weight, scaling⟩ := exponential point
  rw [scaling parameter, scaling lower, scaling upper]
  exact exponential_vector_norm_le_endpoints _ weight parameter lower upper member.1 member.2

theorem exponential_integral_truncations_locally_uniform_right
    {X E : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
    [SecondCountableTopologyEither X E]
    {family : ℂ → X → E}
    (continuous : Continuous (fun input : ℂ × X => family input.1 input.2))
    (exponential : ∀ point, ∃ weight : ℝ, ∀ parameter,
      family parameter point = Complex.exp (parameter * (weight : ℂ)) • family 0 point)
    (measure : Measure X) (threshold : ℝ)
    (integrable : ∀ parameter : ℝ, threshold < parameter → Integrable (family (parameter : ℂ)) measure)
    (domains : ℕ → Set X) (measurable : ∀ index, MeasurableSet (domains index))
    (increasing : Monotone domains) (exhaustive : ∀ point, ∃ index, point ∈ domains index) :
    TendstoLocallyUniformlyOn (fun index parameter => ∫ point in domains index, family parameter point ∂measure)
      (fun parameter => ∫ point, family parameter point ∂measure) atTop
      {parameter : ℂ | threshold < parameter.re} := by
  apply (tendstoLocallyUniformlyOn_iff_forall_isCompact
    (isOpen_lt continuous_const Complex.continuous_re)).mpr
  intro parameters contained compact
  rcases Set.eq_empty_or_nonempty parameters with empty | nonempty
  · subst parameters
    exact tendstoUniformlyOn_empty
  · obtain ⟨lower, lower_in, minimum⟩ := compact.exists_isMinOn nonempty Complex.continuous_re.continuousOn
    obtain ⟨upper, upper_in, maximum⟩ := compact.exists_isMaxOn nonempty Complex.continuous_re.continuousOn
    apply (exponential_integral_truncations_uniform_strip continuous exponential measure
      (lower.re : ℂ) (upper.re : ℂ) (integrable lower.re (contained lower_in))
      (integrable upper.re (contained upper_in)) domains measurable increasing exhaustive).mono
    intro parameter member
    exact ⟨minimum member, maximum member⟩

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
