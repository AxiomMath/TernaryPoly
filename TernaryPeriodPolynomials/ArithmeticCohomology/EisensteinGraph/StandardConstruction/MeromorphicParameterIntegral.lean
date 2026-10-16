module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.AnalyticParameterIntegral

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open MeasureTheory Filter Topology

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.MeromorphicParameterIntegral

def HasAnalyticDomination {α : Type*} [MeasurableSpace α]
    (measure : Measure α) (function : ℂ → α → ℂ) (parameter : ℂ) : Prop :=
  ∃ set : Set ℂ, ∃ bound : α → ℝ, IsOpen set ∧ parameter ∈ set ∧
    (∀ value, AEStronglyMeasurable (function value) measure) ∧
    (∀ argument, DifferentiableOn ℂ (fun value => function value argument) set) ∧
    Integrable bound measure ∧
    ∀ argument value, value ∈ set → ‖function value argument‖ ≤ bound argument

def HasDominatedRegularization {α : Type*} [MeasurableSpace α]
    (measure : Measure α) (function : ℂ → α → ℂ) (parameter : ℂ) : Prop :=
  ∃ order : ℕ, ∃ regularized : ℂ → α → ℂ, ∃ set : Set ℂ, ∃ bound : α → ℝ,
    IsOpen set ∧ parameter ∈ set ∧
    (∀ value, AEStronglyMeasurable (regularized value) measure) ∧
    (∀ argument, DifferentiableOn ℂ (fun value => regularized value argument) set) ∧
    Integrable bound measure ∧
    (∀ argument value, value ∈ set → ‖regularized value argument‖ ≤ bound argument) ∧
    ∀ value ∈ set, value ≠ parameter → ∀ argument,
      regularized value argument = (value - parameter) ^ order * function value argument

theorem integral_analyticAt_of_domination {α : Type*} [MeasurableSpace α]
    (measure : Measure α) (function : ℂ → α → ℂ) (parameter : ℂ)
    (dominated : HasAnalyticDomination measure function parameter) :
    AnalyticAt ℂ (fun value => ∫ argument, function value argument ∂measure) parameter := by
  obtain ⟨set, bound, isOpen, membership, measurable, differentiable, integrable, bounded⟩ := dominated
  exact AnalyticParameterIntegral.integral_analyticAt measure function measurable set isOpen differentiable
    bound integrable bounded parameter membership

theorem integral_meromorphicAt {α : Type*} [MeasurableSpace α]
    (measure : Measure α) (function regularized : ℂ → α → ℂ)
    (parameter : ℂ) (order : ℕ) (set : Set ℂ) (isOpen : IsOpen set) (membership : parameter ∈ set)
    (measurable : ∀ value, AEStronglyMeasurable (regularized value) measure)
    (differentiable : ∀ argument, DifferentiableOn ℂ (fun value => regularized value argument) set)
    (bound : α → ℝ) (integrable : Integrable bound measure)
    (bounded : ∀ argument value, value ∈ set → ‖regularized value argument‖ ≤ bound argument)
    (equality : ∀ value ∈ set, value ≠ parameter → ∀ argument,
      regularized value argument = (value - parameter) ^ order * function value argument) :
    MeromorphicAt (fun value => ∫ argument, function value argument ∂measure) parameter := by
  have analytic := AnalyticParameterIntegral.integral_analyticAt measure regularized measurable
    set isOpen differentiable bound integrable bounded parameter membership
  have denominator : AnalyticAt ℂ (fun value : ℂ => (value - parameter) ^ order) parameter :=
    (analyticAt_id.sub analyticAt_const).pow order
  apply (analytic.meromorphicAt.div denominator.meromorphicAt).congr
  have near : ∀ᶠ value : ℂ in 𝓝[≠] parameter, value ∈ set :=
    nhdsWithin_le_nhds (isOpen.mem_nhds membership)
  filter_upwards [near, self_mem_nhdsWithin] with value valueMembership different
  have nonzero : value - parameter ≠ 0 := sub_ne_zero.mpr different
  change (∫ argument, regularized value argument ∂measure) / (value - parameter) ^ order = _
  simp_rw [equality value valueMembership different]
  rw [integral_const_mul]
  exact mul_div_cancel_left₀ _ (pow_ne_zero order nonzero)

theorem integral_meromorphicAt_of_regularization {α : Type*} [MeasurableSpace α]
    (measure : Measure α) (function : ℂ → α → ℂ) (parameter : ℂ)
    (regularization : HasDominatedRegularization measure function parameter) :
    MeromorphicAt (fun value => ∫ argument, function value argument ∂measure) parameter := by
  obtain ⟨order, regularized, set, bound, isOpen, membership, measurable,
    differentiable, integrable, bounded, equality⟩ := regularization
  exact integral_meromorphicAt measure function regularized parameter order set isOpen membership
    measurable differentiable bound integrable bounded equality

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.MeromorphicParameterIntegral
