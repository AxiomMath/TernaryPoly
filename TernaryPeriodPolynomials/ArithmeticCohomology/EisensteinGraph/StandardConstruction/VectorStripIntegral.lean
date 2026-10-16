module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.StripIntegral

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open MeasureTheory Filter Topology

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.VectorStripIntegral

theorem derivative_aestronglyMeasurable {α : Type*} [MeasurableSpace α]
    (measure : Measure α) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (function : ℂ → α → E)
    (measurable : ∀ parameter, AEStronglyMeasurable (function parameter) measure)
    (differentiable : ∀ argument, Differentiable ℂ (fun parameter => function parameter argument))
    (parameter : ℂ) :
    AEStronglyMeasurable (fun argument => deriv (fun z => function z argument) parameter) measure := by
  apply aestronglyMeasurable_of_tendsto_ae (𝓝[≠] (0 : ℂ))
    (f := fun increment argument => increment⁻¹ •
      (function (parameter + increment) argument - function parameter argument))
  · intro increment
    exact ((measurable (parameter + increment)).sub (measurable parameter)).const_smul (increment⁻¹ : ℂ)
  · exact Eventually.of_forall (fun argument =>
      (differentiable argument parameter).hasDerivAt.tendsto_slope_zero)

theorem integral_differentiableOn_strip {α : Type*} [MeasurableSpace α]
    (measure : Measure α) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (function : ℂ → α → E)
    (measurable : ∀ parameter, AEStronglyMeasurable (function parameter) measure)
    (differentiable : ∀ argument, Differentiable ℂ (fun parameter => function parameter argument))
    (lower upper : ℝ)
    (bounded : ∀ argument parameter, lower ≤ parameter.re → parameter.re ≤ upper →
      ‖function parameter argument‖ ≤ ‖function (lower : ℂ) argument‖ +
        ‖function (upper : ℂ) argument‖)
    (lowerIntegrable : Integrable (function (lower : ℂ)) measure)
    (upperIntegrable : Integrable (function (upper : ℂ)) measure) :
    DifferentiableOn ℂ (fun parameter => ∫ argument, function parameter argument ∂measure)
      {parameter : ℂ | lower < parameter.re ∧ parameter.re < upper} := by
  intro center membership
  obtain ⟨radius, positive, inside⟩ := StripIntegral.sphere_in_strip lower upper center membership.1 membership.2
  have integrable : Integrable (function center) measure :=
    (lowerIntegrable.norm.add upperIntegrable.norm).mono' (measurable center)
      (Eventually.of_forall (fun argument => bounded argument center membership.1.le membership.2.le))
  have boundIntegrable : Integrable (fun argument =>
      (‖function (lower : ℂ) argument‖ + ‖function (upper : ℂ) argument‖) / radius) measure :=
    (lowerIntegrable.norm.add upperIntegrable.norm).div_const radius
  have derivativeBound : ∀ᵐ argument ∂measure, ∀ parameter ∈ Metric.ball center radius,
      ‖deriv (fun z => function z argument) parameter‖ ≤
        (‖function (lower : ℂ) argument‖ + ‖function (upper : ℂ) argument‖) / radius := by
    apply Eventually.of_forall
    intro argument parameter parameterMembership
    apply Complex.norm_deriv_le_of_forall_mem_sphere_norm_le positive
      (differentiable argument).diffContOnCl
    intro value valueMembership
    obtain ⟨lowerBound, upperBound⟩ := inside parameter parameterMembership value valueMembership
    exact bounded argument value lowerBound upperBound
  have derivative := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds center positive) (Eventually.of_forall measurable) integrable
    (derivative_aestronglyMeasurable measure function measurable differentiable center)
    derivativeBound boundIntegrable
    (Eventually.of_forall (fun argument parameter _ => (differentiable argument parameter).hasDerivAt))
  exact derivative.2.differentiableAt.differentiableWithinAt

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.VectorStripIntegral
