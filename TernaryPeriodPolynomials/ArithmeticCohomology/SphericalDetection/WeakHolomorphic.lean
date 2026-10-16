module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.InnerProductSpace.Basic
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
public import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
public import Mathlib.Analysis.Real.Cardinality
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
open scoped Interval

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

theorem continuousLinearMap_circleIntegral (operator : E →L[ℂ] F) (function : ℂ → E)
    (center : ℂ) (radius : ℝ) (integrable : CircleIntegrable function center radius) :
    operator (∮ point in C(center, radius), function point) =
      ∮ point in C(center, radius), operator (function point) := by
  unfold circleIntegral
  rw [← operator.intervalIntegral_comp_comm integrable.out]
  simp only [map_smul]

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem cauchyFormula_of_inner_dense (tests : Set H) (dense : Dense tests)
    (function : ℂ → H) (center point : ℂ) (radius : ℝ) (radius_positive : 0 < radius)
    (continuous : ContinuousOn function (Metric.closedBall center radius))
    (weak : ∀ test ∈ tests, DifferentiableOn ℂ (fun argument => inner ℂ test (function argument))
      (Metric.closedBall center radius)) (point_mem : point ∈ Metric.ball center radius) :
    (2 * (Real.pi : ℂ) * Complex.I)⁻¹ • (∮ argument in C(center, radius), (argument - point)⁻¹ • function argument) =
      function point := by
  have outside : point ∉ Metric.sphere center |radius| := by
    rw [abs_of_pos radius_positive, Metric.mem_sphere]
    exact ne_of_lt point_mem
  have kernel_integrable : CircleIntegrable (fun argument => (argument - point)⁻¹ • function argument) center radius := by
    apply (circleIntegrable_sub_inv_iff.mpr (Or.inr outside)).smul_continuousOn
    rw [abs_of_pos radius_positive]
    exact continuous.mono Metric.sphere_subset_closedBall
  have nonzero : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
  apply dense.eq_of_inner_right ℂ
  intro test test_mem
  change (innerSL ℂ test) (_ • _) = (innerSL ℂ test) (function point)
  rw [map_smul, continuousLinearMap_circleIntegral _ _ _ _ kernel_integrable]
  simp only [map_smul, innerSL_apply_apply]
  rw [(weak test test_mem).circleIntegral_sub_inv_smul point_mem, inv_smul_smul₀ nonzero]

theorem differentiableOn_of_inner_dense (tests : Set H) (dense : Dense tests)
    (function : ℂ → H) (domain : Set ℂ) (domain_open : IsOpen domain)
    (continuous : ContinuousOn function domain)
    (weak : ∀ test ∈ tests, DifferentiableOn ℂ (fun argument => inner ℂ test (function argument)) domain) :
    DifferentiableOn ℂ function domain := by
  intro point member
  obtain ⟨radius, radius_positive, ball_subset⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (domain_open.mem_nhds member)
  have circle_integrable : CircleIntegrable function point radius :=
    (continuous.mono (Metric.sphere_subset_closedBall.trans ball_subset)).circleIntegrable radius_positive.le
  have formula : function =ᶠ[nhds point]
      (fun argument => (2 * (Real.pi : ℂ) * Complex.I)⁻¹ •
        (∮ contour_point in C(point, radius), (contour_point - argument)⁻¹ • function contour_point)) := by
    filter_upwards [Metric.ball_mem_nhds point radius_positive] with argument argument_mem
    exact (cauchyFormula_of_inner_dense tests dense function point argument radius radius_positive
      (continuous.mono ball_subset) (fun test test_mem => (weak test test_mem).mono ball_subset) argument_mem).symm
  have series := hasFPowerSeriesOn_cauchy_integral (R := (⟨radius, radius_positive.le⟩ : NNReal))
    circle_integrable radius_positive
  exact (series.analyticAt.differentiableAt.congr_of_eventuallyEq formula).differentiableWithinAt

end TernaryPeriodPolynomials.SphericalDetection.Helpers
