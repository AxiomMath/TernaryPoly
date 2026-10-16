module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Compact.VectorIntegrals
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.ScaledExponentialBounds

@[expose] public section


open MeasureTheory Filter

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem exponential_family_integrable
    {X E : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [SecondCountableTopologyEither X E]
    {family : ℂ → X → E}
    (continuous : Continuous (fun input : ℂ × X => family input.1 input.2))
    (exponential : ∀ point, ∃ weight : ℝ, ∀ parameter,
      family parameter point = Complex.exp (parameter * (weight : ℂ)) • family 0 point)
    (measure : Measure X) (lower upper parameter : ℂ)
    (lower_integrable : Integrable (family lower) measure)
    (upper_integrable : Integrable (family upper) measure)
    (lower_bound : lower.re ≤ parameter.re) (upper_bound : parameter.re ≤ upper.re) :
    Integrable (family parameter) measure := by
  have measurable : AEStronglyMeasurable (family parameter) measure :=
    (continuous.comp (continuous_const.prodMk continuous_id)).stronglyMeasurable.aestronglyMeasurable
  apply (lower_integrable.norm.add upper_integrable.norm).mono' measurable
  apply Eventually.of_forall
  intro point
  simp only [Pi.add_apply]
  obtain ⟨weight, scaling⟩ := exponential point
  rw [scaling parameter, scaling lower, scaling upper]
  exact exponential_vector_norm_le_endpoints _ weight parameter lower upper lower_bound upper_bound

theorem exponential_integral_hasDerivAt
    {X E : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E] [CompleteSpace E]
    [SecondCountableTopologyEither X E]
    {family : ℂ → X → E}
    (continuous : Continuous (fun input : ℂ × X => family input.1 input.2))
    (exponential : ∀ point, ∃ weight : ℝ, ∀ parameter,
      family parameter point = Complex.exp (parameter * (weight : ℂ)) • family 0 point)
    (measure : Measure X) (lower upper radius : ℝ) (positive : 0 < radius)
    (lower_integrable : Integrable (family ((lower - radius : ℝ) : ℂ)) measure)
    (upper_integrable : Integrable (family ((upper + radius : ℝ) : ℂ)) measure)
    (parameter : ℂ) (lower_bound : lower < parameter.re) (upper_bound : parameter.re < upper) :
    Integrable (fun point => deriv (fun nearby => family nearby point) parameter) measure ∧
    HasDerivAt (fun nearby => ∫ point, family nearby point ∂measure)
      (∫ point, deriv (fun nearby => family nearby point) parameter ∂measure) parameter := by
  let interval : Set ℂ := {nearby | lower < nearby.re ∧ nearby.re < upper}
  have open_interval : IsOpen interval :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have parameter_integrable := exponential_family_integrable continuous exponential measure
    ((lower - radius : ℝ) : ℂ) ((upper + radius : ℝ) : ℂ) parameter
    lower_integrable upper_integrable (by simp only [Complex.ofReal_re]; linarith)
      (by simp only [Complex.ofReal_re]; linarith)
  apply hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := family)
    (F' := fun nearby point => deriv (fun argument => family argument point) nearby)
    (open_interval.mem_nhds ⟨lower_bound, upper_bound⟩)
    (Eventually.of_forall (fun nearby =>
      (show Continuous (family nearby) from
        continuous.comp (continuous_const.prodMk continuous_id)).stronglyMeasurable.aestronglyMeasurable))
    parameter_integrable (continuous_family_deriv_stronglyMeasurable continuous parameter).aestronglyMeasurable
    (bound := fun point =>
      (‖family ((lower - radius : ℝ) : ℂ) point‖ + ‖family ((upper + radius : ℝ) : ℂ) point‖) / radius)
  · apply Eventually.of_forall
    intro point nearby nearby_in
    obtain ⟨weight, scaling⟩ := exponential point
    rw [funext scaling, scaling ((lower - radius : ℝ) : ℂ), scaling ((upper + radius : ℝ) : ℂ)]
    exact exponential_vector_deriv_norm_le_scaled _ weight lower upper radius nearby positive
      nearby_in.1.le nearby_in.2.le
  · exact (lower_integrable.norm.add upper_integrable.norm).div_const radius
  · exact Eventually.of_forall (fun point nearby _ =>
      (exponential_family_analytic exponential point nearby).differentiableAt.hasDerivAt)

theorem exponential_integral_analytic_right
    {X E : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E] [CompleteSpace E]
    [SecondCountableTopologyEither X E]
    {family : ℂ → X → E}
    (continuous : Continuous (fun input : ℂ × X => family input.1 input.2))
    (exponential : ∀ point, ∃ weight : ℝ, ∀ parameter,
      family parameter point = Complex.exp (parameter * (weight : ℂ)) • family 0 point)
    (measure : Measure X) (threshold : ℝ)
    (integrable : ∀ parameter : ℝ, threshold < parameter → Integrable (family (parameter : ℂ)) measure) :
    AnalyticOnNhd ℂ (fun nearby => ∫ point, family nearby point ∂measure)
      {parameter : ℂ | threshold < parameter.re} := by
  apply DifferentiableOn.analyticOnNhd _ (isOpen_lt continuous_const Complex.continuous_re)
  intro parameter large
  change threshold < parameter.re at large
  let radius : ℝ := (parameter.re - threshold) / 4
  have positive : 0 < radius := by dsimp [radius]; linarith
  have lower_integrable := integrable (parameter.re - radius - radius) (by dsimp [radius]; linarith)
  have upper_integrable := integrable (parameter.re + radius + radius) (by dsimp [radius]; linarith)
  exact (exponential_integral_hasDerivAt continuous exponential measure
    (parameter.re - radius) (parameter.re + radius) radius positive lower_integrable upper_integrable
    parameter (by linarith) (by linarith)).2.differentiableAt.differentiableWithinAt

theorem exponential_compact_integral_analytic
    {X E : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] [T2Space X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E] [CompleteSpace E]
    [SecondCountableTopologyEither X E]
    {family : ℂ → X → E}
    (continuous : Continuous (fun input : ℂ × X => family input.1 input.2))
    (exponential : ∀ point, ∃ weight : ℝ, ∀ parameter,
      family parameter point = Complex.exp (parameter * (weight : ℂ)) • family 0 point)
    (measure : Measure X) [IsFiniteMeasureOnCompacts measure]
    {domain : Set X} (compact : IsCompact domain) (parameter : ℂ) :
    AnalyticAt ℂ (fun nearby => ∫ point in domain, family nearby point ∂measure) parameter := by
  apply exponential_integral_analytic_right continuous exponential (measure.restrict domain)
    (parameter.re - 1) _ parameter (by simp)
  intro nearby _
  exact ContinuousOn.integrableOn_compact compact
    (continuous.comp (continuous_const.prodMk continuous_id)).continuousOn

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
