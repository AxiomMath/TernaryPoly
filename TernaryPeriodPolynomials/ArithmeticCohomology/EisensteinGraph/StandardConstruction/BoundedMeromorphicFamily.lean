module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.BoundedHolomorphicFamily
public import Mathlib.Analysis.Meromorphic.NormalForm
public import Mathlib.Topology.Instances.Discrete
public import Mathlib.Analysis.Meromorphic.IsolatedZeros

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open Filter Topology

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.BoundedMeromorphicFamily

variable {Space : Type*} [TopologicalSpace Space]

theorem map_meromorphic {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (map : E →L[ℂ] F) {function : ℂ → E} {center : ℂ}
    (meromorphic : MeromorphicAt function center) :
    MeromorphicAt (fun parameter => map (function parameter)) center := by
  obtain ⟨order, regular, analytic, equality⟩ :=
    MeromorphicAt.iff_eventuallyEq_zpow_smul_analyticAt.mp meromorphic
  apply MeromorphicAt.iff_eventuallyEq_zpow_smul_analyticAt.mpr
  refine ⟨order, fun parameter => map (regular parameter), (map.analyticAt _).comp analytic, ?_⟩
  filter_upwards [equality] with parameter equality
  rw [equality, map_smul]

theorem nonnegative_order
    {function : ℂ → BoundedContinuousFunction Space ℂ} {center : ℂ}
    (meromorphic : MeromorphicAt function center)
    (pointwise : ∀ point, 0 ≤ meromorphicOrderAt (fun parameter => function parameter point) center) :
    0 ≤ meromorphicOrderAt function center := by
  by_cases infinite : meromorphicOrderAt function center = ⊤
  · rw [infinite]
    exact le_top
  obtain ⟨order, order_eq⟩ := WithTop.ne_top_iff_exists.mp infinite
  obtain ⟨regular, analytic, nonzero, equality⟩ :=
    (meromorphicOrderAt_eq_int_iff meromorphic).mp order_eq.symm
  obtain ⟨point, valueNonzero⟩ : ∃ point, regular center point ≠ 0 := by
    by_contra absent
    apply nonzero
    ext point
    exact not_ne_iff.mp (fun different => absent ⟨point, different⟩)
  have scalarOrder : meromorphicOrderAt (fun parameter => function parameter point) center = order := by
    apply (meromorphicOrderAt_eq_int_iff
      (map_meromorphic (BoundedContinuousFunction.evalCLM ℂ point) meromorphic)).mpr
    refine ⟨fun parameter => regular parameter point,
      ((BoundedContinuousFunction.evalCLM (β := ℂ) ℂ point).analyticAt (regular center)).comp analytic, valueNonzero, ?_⟩
    filter_upwards [equality] with parameter equality
    exact congrArg (fun value : BoundedContinuousFunction Space ℂ => value point) equality
  rw [← order_eq, ← scalarOrder]
  exact pointwise point

theorem eventually_bounded
    {function : ℂ → BoundedContinuousFunction Space ℂ} {center : ℂ}
    (meromorphic : MeromorphicAt function center)
    (pointwise : ∀ point, 0 ≤ meromorphicOrderAt (fun parameter => function parameter point) center) :
    ∃ bound : ℝ, ∀ᶠ parameter in 𝓝[≠] center, ∀ point, ‖function parameter point‖ ≤ bound := by
  have analytic := meromorphic.meromorphicOrderAt_nonneg_iff_analyticAt_toMeromorphicNFAt.mp
    (nonnegative_order meromorphic pointwise)
  obtain ⟨bound, bounded⟩ := analytic.continuousAt.norm.isBoundedUnder_le
  refine ⟨bound, ?_⟩
  filter_upwards [bounded.filter_mono nhdsWithin_le_nhds,
    meromorphic.eq_nhdsNE_toMeromorphicNFAt] with parameter bounded equality
  intro point
  rw [equality]
  exact ((toMeromorphicNFAt function center parameter).norm_coe_le_norm point).trans bounded

abbrev BoundedFunctions (Space : Type*) := BoundedContinuousFunction (WithDiscreteTopology Space) ℂ

def ofBounded {Space : Type*} (function : Space → ℂ)
    (bounded : ∃ bound : ℝ, ∀ point, ‖function point‖ ≤ bound) : BoundedFunctions Space :=
  BoundedContinuousFunction.mkOfDiscrete (fun point => function point.ofTopology) (2 * bounded.choose) (fun first second =>
    (dist_le_norm_add_norm _ _).trans (by linarith [bounded.choose_spec first.ofTopology, bounded.choose_spec second.ofTopology]))

theorem ofBounded_apply {Space : Type*} (function : Space → ℂ)
    (bounded : ∃ bound : ℝ, ∀ point, ‖function point‖ ≤ bound) (point : Space) :
    ofBounded function bounded (.toTopology ⊥ point) = function point := rfl

theorem differentiable {Space : Type*} (function : ℂ → Space → ℂ)
    (holomorphic : ∀ point, Differentiable ℂ (fun parameter => function parameter point))
    (bounded : ∀ compact : Set ℂ, IsCompact compact →
      ∃ bound : ℝ, 0 ≤ bound ∧ ∀ parameter ∈ compact, ∀ point, ‖function parameter point‖ ≤ bound) :
    ∃ family : ℂ → BoundedFunctions Space,
      Differentiable ℂ family ∧ ∀ parameter point, family parameter (.toTopology ⊥ point) = function parameter point := by
  have atParameter (parameter : ℂ) : ∃ bound : ℝ, ∀ point, ‖function parameter point‖ ≤ bound := by
    obtain ⟨bound, _, bounds⟩ := bounded {parameter} isCompact_singleton
    exact ⟨bound, bounds parameter (Set.mem_singleton _)⟩
  let family := fun parameter => ofBounded (function parameter) (atParameter parameter)
  refine ⟨family, ?_, fun _ _ => rfl⟩
  apply differentiableOn_univ.mp
  apply BoundedHolomorphicFamily.boundedHolomorphicFamily_differentiableOn_of_localBound
    family Set.univ isOpen_univ (fun point => (holomorphic point.ofTopology).differentiableOn)
  intro center _
  obtain ⟨bound, nonnegative, bounds⟩ := bounded (Metric.closedBall center 2) (isCompact_closedBall center 2)
  refine ⟨1, zero_lt_one, Set.subset_univ _, bound, ?_⟩
  intro parameter membership
  apply (BoundedContinuousFunction.norm_le nonnegative).mpr
  intro point
  exact bounds parameter (Metric.ball_subset_closedBall (by simpa using membership)) point.ofTopology

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.BoundedMeromorphicFamily
