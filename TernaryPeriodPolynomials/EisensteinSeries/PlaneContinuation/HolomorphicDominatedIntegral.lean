module

public import Mathlib.Analysis.Complex.Schwarz
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Algebra.Algebra.TransferInstance
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
public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
public import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Data.List.Enum
public import Mathlib.Data.Nat.Choose.Cast
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
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
public import Mathlib.RingTheory.Finiteness.Lattice
public import Mathlib.RingTheory.SimpleRing.Matrix
public import Mathlib.SetTheory.Cardinal.ENNReal
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Tactic.Basify.Attr
public import Mathlib.Topology.Algebra.IsUniformGroup.Order
public import Mathlib.Topology.Order.AtTopBotIxx
public import Mathlib.Topology.Order.ExtrClosure
public import Mathlib.Topology.WithTopology

@[expose] public section


open MeasureTheory Filter

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.HolomorphicDominatedIntegral

variable {Space : Type*} [MeasurableSpace Space]

theorem derivative_measurable (function : ℂ → Space → ℂ)
    (measurable : ∀ parameter, Measurable (function parameter))
    (holomorphic : ∀ point, Differentiable ℂ (fun parameter => function parameter point)) (center : ℂ) :
    Measurable (fun point => deriv (fun parameter => function parameter point) center) := by
  let step : ℕ → ℂ := fun index => 1 / ((index : ℂ) + 1)
  have nonzero : ∀ index, step index ≠ 0 := by
    intro index
    apply div_ne_zero one_ne_zero
    exact_mod_cast Nat.succ_ne_zero index
  have converges : Tendsto step atTop (nhdsWithin 0 {0}ᶜ) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall (fun index => nonzero index)⟩
  apply measurable_of_tendsto_metrizable
    (f := fun index point => (step index)⁻¹ * (function (center + step index) point - function center point))
    (fun index => measurable_const.mul ((measurable _).sub (measurable _)))
  apply tendsto_pi_nhds.mpr
  intro point
  exact ((holomorphic point center).hasDerivAt.tendsto_slope_zero).comp converges

theorem derivative_bound (function : ℂ → ℂ) (holomorphic : Differentiable ℂ function)
    (center parameter : ℂ) (nearby : parameter ∈ Metric.ball center 1) (bound : ℝ)
    (bounded : ∀ value ∈ Metric.ball center 2, ‖function value‖ ≤ bound) :
    ‖deriv function parameter‖ ≤ 2 * bound := by
  have parameterIn : parameter ∈ Metric.ball center 2 :=
    Metric.ball_subset_ball (by norm_num) nearby
  have inclusion : Metric.ball parameter 1 ⊆ Metric.ball center 2 := by
    intro value membership
    have triangle := dist_triangle value parameter center
    have first := Metric.mem_ball.mp membership
    have second := Metric.mem_ball.mp nearby
    exact Metric.mem_ball.mpr (by linarith)
  have maps : Set.MapsTo function (Metric.ball parameter 1) (Metric.closedBall (function parameter) (2 * bound)) := by
    intro value membership
    apply Metric.mem_closedBall.mpr
    rw [dist_eq_norm]
    exact (norm_sub_le _ _).trans (by linarith [bounded value (inclusion membership), bounded parameter parameterIn])
  simpa only [div_one] using Complex.norm_deriv_le_div_of_mapsTo_ball holomorphic.differentiableOn maps zero_lt_one

theorem differentiable (measure : Measure Space) (function : ℂ → Space → ℂ)
    (measurable : ∀ parameter, Measurable (function parameter))
    (holomorphic : ∀ point, Differentiable ℂ (fun parameter => function parameter point))
    (dominated : ∀ center : ℂ, ∃ bound : Space → ℝ, Integrable bound measure ∧
      ∀ parameter ∈ Metric.ball center 2, ∀ point, ‖function parameter point‖ ≤ bound point) :
    Differentiable ℂ (fun parameter => ∫ point, function parameter point ∂measure) := by
  intro center
  obtain ⟨bound, integrableBound, bounded⟩ := dominated center
  have atCenter : Integrable (function center) measure :=
    integrableBound.mono' (measurable center).aestronglyMeasurable
      (Eventually.of_forall (bounded center (Metric.mem_ball_self (by norm_num))))
  have result := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := function) (F' := fun parameter point => deriv (fun parameter => function parameter point) parameter)
    (s := Metric.ball center 1) (bound := fun point => 2 * bound point)
    (Metric.ball_mem_nhds center zero_lt_one)
    (Eventually.of_forall (fun parameter => (measurable parameter).aestronglyMeasurable)) atCenter
    (derivative_measurable function measurable holomorphic center).aestronglyMeasurable
    (Eventually.of_forall (fun point parameter nearby =>
      derivative_bound (fun parameter => function parameter point) (holomorphic point) center parameter nearby
        (bound point) (fun value membership => bounded value membership point)))
    (integrableBound.const_mul 2)
    (Eventually.of_forall (fun point parameter _ => (holomorphic point parameter).hasDerivAt))
  exact result.2.differentiableAt

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.HolomorphicDominatedIntegral
