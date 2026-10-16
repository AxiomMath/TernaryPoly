module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Normalized.VectorContinuity
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.FDeriv.Measurable

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory Filter

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem continuous_family_deriv_stronglyMeasurable
    {X E : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [SecondCountableTopologyEither X E]
    {family : ℂ → X → E}
    (continuous : Continuous (fun input : ℂ × X => family input.1 input.2))
    (parameter : ℂ) :
    StronglyMeasurable (fun point => deriv (fun nearby => family nearby point) parameter) := by
  have swapped : Continuous (Function.uncurry (fun point nearby => family nearby point)) :=
    continuous.comp continuous_swap
  exact (stronglyMeasurable_deriv_with_param swapped).comp_measurable
    (measurable_id.prodMk measurable_const)

theorem normalizedCuspVector_compact_integrable
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family)
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] [T2Space X]
    (measure : Measure X) [IsFiniteMeasureOnCompacts measure]
    {map : X → AdelicGL} (continuous : Continuous map)
    {domain : Set X} (compact : IsCompact domain) (parameter : ℂ) :
    IntegrableOn (fun point => (normalizedCuspVector flat.1 parameter (map point)).val) domain measure :=
  ContinuousOn.integrableOn_compact compact
    ((normalizedCuspVector_continuous flat.1 parameter).comp continuous).continuousOn

theorem normalizedCuspVector_compact_integral_hasDerivAt
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family)
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] [T2Space X]
    [SecondCountableTopology X]
    (measure : Measure X) [IsFiniteMeasureOnCompacts measure]
    {map : X → AdelicGL} (continuous : Continuous map)
    {domain : Set X} (compact : IsCompact domain) (parameter : ℂ) :
    IntegrableOn (fun point => deriv (fun nearby =>
      (normalizedCuspVector flat.1 nearby (map point)).val) parameter) domain measure ∧
    HasDerivAt (fun nearby => ∫ point in domain,
      (normalizedCuspVector flat.1 nearby (map point)).val ∂measure)
      (∫ point in domain, deriv (fun nearby =>
        (normalizedCuspVector flat.1 nearby (map point)).val) parameter ∂measure) parameter := by
  let lower : ℝ := parameter.re - 1
  let upper : ℝ := parameter.re + 1
  let interval : Set ℂ := {nearby | lower < nearby.re ∧ nearby.re < upper}
  have open_interval : IsOpen interval :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have member : parameter ∈ interval := by
    dsimp [interval, lower, upper]
    constructor <;> linarith
  have joint := (normalizedCuspVector_joint_continuous flat).comp
    (continuous_fst.prodMk (continuous.comp continuous_snd))
  dsimp only [Function.comp_def] at joint
  have measurable_deriv := continuous_family_deriv_stronglyMeasurable
    (family := fun nearby point => (normalizedCuspVector flat.1 nearby (map point)).val) joint parameter
  obtain ⟨bound, _, bounded⟩ := normalizedCuspVector_compact_deriv_bound flat
    (map '' domain) (compact.image continuous) lower upper
  apply hasDerivAt_integral_of_dominated_loc_of_deriv_le (open_interval.mem_nhds member)
    (Eventually.of_forall (fun nearby =>
      (normalizedCuspVector_compact_integrable flat measure continuous compact nearby).aestronglyMeasurable))
    (normalizedCuspVector_compact_integrable flat measure continuous compact parameter)
    measurable_deriv.aestronglyMeasurable
    (bound := fun _ => bound)
  · filter_upwards [ae_restrict_mem compact.measurableSet] with point point_in
    intro nearby nearby_in
    exact bounded nearby nearby_in.1.le nearby_in.2.le (map point) ⟨point, point_in, rfl⟩
  · exact ContinuousOn.integrableOn_compact compact continuous_const.continuousOn
  · exact Eventually.of_forall (fun point nearby _ =>
      (normalizedCuspVector_analytic flat (map point) nearby).differentiableAt.hasDerivAt)

theorem normalizedCuspVector_compact_integral_analytic
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family)
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] [T2Space X]
    [SecondCountableTopology X]
    (measure : Measure X) [IsFiniteMeasureOnCompacts measure]
    {map : X → AdelicGL} (continuous : Continuous map)
    {domain : Set X} (compact : IsCompact domain) (parameter : ℂ) :
    AnalyticAt ℂ (fun nearby => ∫ point in domain,
      (normalizedCuspVector flat.1 nearby (map point)).val ∂measure) parameter :=
  (show Differentiable ℂ _ from fun nearby =>
    (normalizedCuspVector_compact_integral_hasDerivAt flat measure continuous compact nearby).2.differentiableAt).analyticAt parameter

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
