module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Compact.ParameterIntegral

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open MeasureTheory Filter Topology

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.AnalyticParameterIntegral

theorem derivative_measurable {α : Type*} [MeasurableSpace α]
    (measure : Measure α) (function : ℂ → α → ℂ)
    (measurable : ∀ parameter, AEStronglyMeasurable (function parameter) measure)
    (parameter : ℂ)
    (differentiable : ∀ argument, DifferentiableAt ℂ (fun z => function z argument) parameter) :
    AEStronglyMeasurable (fun argument => deriv (fun z => function z argument) parameter) measure := by
  apply aestronglyMeasurable_of_tendsto_ae (𝓝[≠] (0 : ℂ))
    (f := fun increment argument => increment⁻¹ •
      (function (parameter + increment) argument - function parameter argument))
  · intro increment
    exact ((measurable (parameter + increment)).sub (measurable parameter)).const_smul (increment⁻¹ : ℂ)
  · exact Eventually.of_forall (fun argument => (differentiable argument).hasDerivAt.tendsto_slope_zero)

theorem integral_differentiableOn {α : Type*} [MeasurableSpace α]
    (measure : Measure α) (function : ℂ → α → ℂ)
    (measurable : ∀ parameter, AEStronglyMeasurable (function parameter) measure)
    (set : Set ℂ) (isOpen : IsOpen set)
    (differentiable : ∀ argument, DifferentiableOn ℂ (fun z => function z argument) set)
    (bound : α → ℝ) (boundIntegrable : Integrable bound measure)
    (bounded : ∀ argument parameter, parameter ∈ set → ‖function parameter argument‖ ≤ bound argument) :
    DifferentiableOn ℂ (fun parameter => ∫ argument, function parameter argument ∂measure) set := by
  intro center membership
  obtain ⟨radius, positive, inside⟩ := Metric.isOpen_iff.mp isOpen center membership
  have smallPositive : 0 < radius / 3 := div_pos positive (by norm_num)
  have smallInside : Metric.ball center (radius / 3) ⊆ set :=
    (Metric.ball_subset_ball (by linarith)).trans inside
  have closedInside : ∀ parameter ∈ Metric.ball center (radius / 3),
      Metric.closedBall parameter (radius / 3) ⊆ set := by
    intro parameter near
    apply Set.Subset.trans _ inside
    apply Metric.closedBall_subset_ball'
    have distance := Metric.mem_ball.mp near
    linarith
  have integrable : Integrable (function center) measure :=
    boundIntegrable.mono' (measurable center) (Eventually.of_forall (fun argument => bounded argument center membership))
  have derivativeBound : ∀ᵐ argument ∂measure, ∀ parameter ∈ Metric.ball center (radius / 3),
      ‖deriv (fun z => function z argument) parameter‖ ≤ bound argument / (radius / 3) := by
    apply Eventually.of_forall
    intro argument parameter near
    apply Complex.norm_deriv_le_of_forall_mem_sphere_norm_le smallPositive
      ((differentiable argument).diffContOnCl_ball (closedInside parameter near))
    intro value sphere
    exact bounded argument value (closedInside parameter near (Metric.sphere_subset_closedBall sphere))
  have derivative := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds center smallPositive) (Eventually.of_forall measurable) integrable
    (derivative_measurable measure function measurable center
      (fun argument => (differentiable argument).differentiableAt (isOpen.mem_nhds membership)))
    derivativeBound (boundIntegrable.div_const (radius / 3))
    (Eventually.of_forall (fun argument parameter near =>
      ((differentiable argument).differentiableAt (isOpen.mem_nhds (smallInside near))).hasDerivAt))
  exact derivative.2.differentiableAt.differentiableWithinAt

theorem integral_analyticAt {α : Type*} [MeasurableSpace α]
    (measure : Measure α) (function : ℂ → α → ℂ)
    (measurable : ∀ parameter, AEStronglyMeasurable (function parameter) measure)
    (set : Set ℂ) (isOpen : IsOpen set)
    (differentiable : ∀ argument, DifferentiableOn ℂ (fun z => function z argument) set)
    (bound : α → ℝ) (boundIntegrable : Integrable bound measure)
    (bounded : ∀ argument parameter, parameter ∈ set → ‖function parameter argument‖ ≤ bound argument)
    (parameter : ℂ) (membership : parameter ∈ set) :
    AnalyticAt ℂ (fun parameter => ∫ argument, function parameter argument ∂measure) parameter :=
  (integral_differentiableOn measure function measurable set isOpen differentiable
    bound boundIntegrable bounded).analyticAt (isOpen.mem_nhds membership)

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.AnalyticParameterIntegral
