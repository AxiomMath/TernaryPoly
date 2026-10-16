module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Pointwise.Set.Card
public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Interval.Set.Group
public import Mathlib.Algebra.Order.Monoid.Canonical.Basic
public import Mathlib.Algebra.Order.Ring.Interval
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.Analysis.Analytic.Within
public import Mathlib.Analysis.Calculus.Deriv.AffineMap
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import Mathlib.Data.List.Enum
public import Mathlib.Data.Nat.NthRoot.Defs
public import Mathlib.Data.String.Defs
public import Mathlib.GroupTheory.QuotientGroup.ModEq
public import Mathlib.Lean.Elab.InfoTree
public import Mathlib.Lean.Elab.Tactic.Basic
public import Mathlib.Lean.Elab.Tactic.Meta
public import Mathlib.Lean.Expr.ExtraRecognizers
public import Mathlib.Lean.Expr.Rat
public import Mathlib.Lean.GoalsLocation
public import Mathlib.Lean.MessageData.Trace
public import Mathlib.Lean.Meta
public import Mathlib.Lean.Meta.Basic
public import Mathlib.Lean.Meta.KAbstractPositions
public import Mathlib.Lean.Meta.Tactic.Rewrite
public import Mathlib.Lean.PrettyPrinter.Delaborator
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
public import Mathlib.RingTheory.Finiteness.Lattice
public import Mathlib.RingTheory.SimpleRing.Matrix
public import Mathlib.SetTheory.Cardinal.ENNReal
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Tactic.Basify.Attr
public import Mathlib.Topology.Algebra.IsUniformGroup.Order
public import Mathlib.Topology.Order.AtTopBotIxx
public import Mathlib.Topology.WithTopology

@[expose] public section


open MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem hasFDerivAt_integral_compact_parameter
    {P X E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [ProperSpace P]
    [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (measure : Measure X) [IsFiniteMeasure measure]
    (values : P → X → E) (derivatives : P → X → P →L[ℝ] E)
    (domain : Set P) (domain_open : IsOpen domain)
    (continuous : ContinuousOn (Function.uncurry values) (domain ×ˢ Set.univ))
    (derivative_continuous : ContinuousOn (Function.uncurry derivatives) (domain ×ˢ Set.univ))
    (has_derivative : ∀ point ∈ domain, ∀ argument,
      HasFDerivAt (fun point => values point argument) (derivatives point argument) point)
    (point : P) (member : point ∈ domain) :
    HasFDerivAt (fun point => ∫ argument, values point argument ∂measure)
      (∫ argument, derivatives point argument ∂measure) point := by
  obtain ⟨radius, radius_positive, ball_subset⟩ :=
    Metric.nhds_basis_closedBall.mem_iff.mp (domain_open.mem_nhds member)
  have compact : IsCompact (Metric.closedBall point radius ×ˢ (Set.univ : Set X)) :=
    (isCompact_closedBall point radius).prod isCompact_univ
  obtain ⟨bound, bounded⟩ := compact.exists_bound_of_continuousOn
    (derivative_continuous.mono (Set.prod_mono ball_subset (Set.Subset.refl _)))
  have values_continuous (parameter : P) (parameter_mem : parameter ∈ domain) : Continuous (values parameter) :=
    continuous.comp_continuous (continuous_const.prodMk continuous_id) (fun _ => ⟨parameter_mem, Set.mem_univ _⟩)
  have derivatives_continuous : Continuous (derivatives point) :=
    derivative_continuous.comp_continuous (continuous_const.prodMk continuous_id) (fun _ => ⟨member, Set.mem_univ _⟩)
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := measure)
    (s := Metric.closedBall point radius) (bound := fun _ => bound)
    (Metric.closedBall_mem_nhds point radius_positive)
  · filter_upwards [domain_open.mem_nhds member] with parameter parameter_mem
    exact (values_continuous parameter parameter_mem).aestronglyMeasurable
  · exact (values_continuous point member).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · exact derivatives_continuous.aestronglyMeasurable
  · filter_upwards [] with argument parameter parameter_mem
    exact bounded (parameter, argument) ⟨parameter_mem, Set.mem_univ _⟩
  · exact integrable_const bound
  · filter_upwards [] with argument parameter parameter_mem
    exact has_derivative parameter (ball_subset parameter_mem) argument

theorem hasDerivAt_integral_compact_parameter
    {X E : Type}
    [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (measure : Measure X) [IsFiniteMeasure measure]
    (values derivatives : ℝ → X → E) (domain : Set ℝ) (domain_open : IsOpen domain)
    (continuous : ContinuousOn (Function.uncurry values) (domain ×ˢ Set.univ))
    (derivative_continuous : ContinuousOn (Function.uncurry derivatives) (domain ×ˢ Set.univ))
    (has_derivative : ∀ point ∈ domain, ∀ argument,
      HasDerivAt (fun point => values point argument) (derivatives point argument) point)
    (point : ℝ) (member : point ∈ domain) :
    HasDerivAt (fun point => ∫ argument, values point argument ∂measure)
      (∫ argument, derivatives point argument ∂measure) point := by
  let linear : ℝ → X → ℝ →L[ℝ] E := fun point argument =>
    (1 : ℝ →L[ℝ] ℝ).smulRight (derivatives point argument)
  have linear_continuous : ContinuousOn (Function.uncurry linear) (domain ×ˢ Set.univ) :=
    continuousOn_clm_apply.mpr (fun _ => continuousOn_const.smul derivative_continuous)
  have derivative := hasFDerivAt_integral_compact_parameter measure values linear domain domain_open
    continuous linear_continuous has_derivative point member
  have integrable : Integrable (linear point) measure :=
    (linear_continuous.comp_continuous (continuous_const.prodMk continuous_id)
      (fun _ => ⟨member, Set.mem_univ _⟩)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have evaluated := derivative.hasDerivAt
  rw [ContinuousLinearMap.integral_apply integrable] at evaluated
  simpa only [linear, ContinuousLinearMap.smulRight_apply, one_apply_eq_self, one_smul] using evaluated

end TernaryPeriodPolynomials.SphericalDetection.Helpers
