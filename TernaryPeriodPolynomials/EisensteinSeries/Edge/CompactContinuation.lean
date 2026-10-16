module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Line.CompactContinuation

@[expose] public section


/-!
# Continuations that are meromorphic families of continuous functions on compact sets

`Regular continuation` says: for every compact space `T` mapped continuously into `GL₃(𝔸)`, the
functions `t ↦ continuation s (embed t)` form a meromorphic family `ℂ → C(T)` of bounded continuous
functions. This strengthens `LineCompactContinuation.Regular` (bounded functions on one fixed
domain along the line radical, with the discrete topology) in two ways: every compact set is
allowed, and the functions are continuous. The first gives uniform bounds near `s₀` on the plane
radical domain, the second gives continuity of the value at `s₀`.

This file proves that the property is stable under multiplication by meromorphic scalars, finite
sums, right translation and the finite-level average, and gives the construction of such a family
from pointwise holomorphic, slice-continuous, locally bounded functions.

Original work by Claude Opus 5.5 (AxiomCode).
-/

open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory Filter Topology
open TernaryPeriodPolynomials.PlaneEisensteinContinuation
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction

noncomputable section

namespace TernaryPeriodPolynomials.EdgeEisenstein.CompactContinuation

/-- On every compact space mapped continuously into `GL₃(𝔸)`, the continuation is a meromorphic
family of bounded continuous functions. -/
def Regular (continuation : ℂ → AdelicGL → ℂ) : Prop :=
  ∀ (Space : Type) [TopologicalSpace Space] [CompactSpace Space] (embed : Space → AdelicGL),
    Continuous embed → ∃ family : ℂ → BoundedContinuousFunction Space ℂ,
      (∀ parameter, MeromorphicAt family parameter) ∧
      ∀ parameter point, family parameter point = continuation parameter (embed point)

theorem regular_mul {continuation : ℂ → AdelicGL → ℂ} (regular : Regular continuation)
    (coefficient : ℂ → ℂ) (meromorphic : ∀ parameter, MeromorphicAt coefficient parameter) :
    Regular (fun parameter point => coefficient parameter * continuation parameter point) := by
  intro Space _ _ embed continuous
  obtain ⟨family, familyMeromorphic, equality⟩ := regular Space embed continuous
  refine ⟨fun parameter => coefficient parameter • family parameter,
    fun parameter => (meromorphic parameter).smul (familyMeromorphic parameter), ?_⟩
  intro parameter point
  change coefficient parameter * family parameter point = _
  rw [equality]

theorem regular_sum {Index : Type} (indices : Finset Index)
    (continuations : Index → ℂ → AdelicGL → ℂ)
    (regular : ∀ index ∈ indices, Regular (continuations index)) :
    Regular (fun parameter point => ∑ index ∈ indices, continuations index parameter point) := by
  classical
  intro Space _ _ embed continuous
  have existsFamily (index : Index) : ∃ family : ℂ → BoundedContinuousFunction Space ℂ,
      (∀ parameter, MeromorphicAt family parameter) ∧
      ∀ parameter point, index ∈ indices → family parameter point =
        continuations index parameter (embed point) := by
    by_cases membership : index ∈ indices
    · obtain ⟨family, meromorphic, equality⟩ := regular index membership Space embed continuous
      exact ⟨family, meromorphic, fun parameter point _ => equality parameter point⟩
    · exact ⟨fun _ => 0, fun _ => MeromorphicAt.const _ _, fun _ _ h => (membership h).elim⟩
  choose families meromorphic equality using existsFamily
  refine ⟨fun parameter => ∑ index ∈ indices, families index parameter,
    fun parameter => MeromorphicAt.fun_sum (fun index _ => meromorphic index parameter), ?_⟩
  intro parameter point
  simp only [BoundedContinuousFunction.sum_apply]
  exact Finset.sum_congr rfl (fun index membership => equality index parameter point membership)

theorem regular_right {continuation : ℂ → AdelicGL → ℂ} (regular : Regular continuation)
    (matrix : AdelicGL) :
    Regular (fun parameter point => continuation parameter (point * matrix)) := by
  intro Space _ _ embed continuous
  obtain ⟨family, meromorphic, equality⟩ :=
    regular Space (fun point => embed point * matrix) (continuous.mul continuous_const)
  exact ⟨family, meromorphic, fun parameter point => equality parameter point⟩

theorem regular_average {degree : ℕ} (data : InducingData degree)
    {continuation : ℂ → AdelicGL → ℂ} (regular : Regular continuation) :
    Regular (fun parameter => FiniteSectionProjection.average data (continuation parameter)) :=
  regular_mul
    (regular_sum Finset.univ _ (fun index _ => regular_right regular
      (FiniteSectionProjection.inclusion (FiniteSectionProjection.representative data index))))
    (fun _ => (Fintype.card (FiniteSectionProjection.levelImage data) : ℂ)⁻¹)
    (fun _ => analyticAt_const.meromorphicAt)

/-- A family of continuous functions on a compact space, holomorphic in the parameter at every
point and bounded uniformly on compact sets of parameters, is a holomorphic family of bounded
continuous functions. -/
theorem differentiable_of_continuous {Space : Type} [TopologicalSpace Space] [CompactSpace Space]
    (function : ℂ → Space → ℂ)
    (continuous : ∀ parameter, Continuous (function parameter))
    (holomorphic : ∀ point, Differentiable ℂ (fun parameter => function parameter point))
    (bounded : ∀ compact : Set ℂ, IsCompact compact →
      ∃ bound : ℝ, 0 ≤ bound ∧ ∀ parameter ∈ compact, ∀ point, ‖function parameter point‖ ≤ bound) :
    ∃ family : ℂ → BoundedContinuousFunction Space ℂ,
      Differentiable ℂ family ∧ ∀ parameter point, family parameter point = function parameter point := by
  let family : ℂ → BoundedContinuousFunction Space ℂ := fun parameter =>
    BoundedContinuousFunction.mkOfCompact ⟨function parameter, continuous parameter⟩
  refine ⟨family, ?_, fun _ _ => rfl⟩
  apply differentiableOn_univ.mp
  apply BoundedHolomorphicFamily.boundedHolomorphicFamily_differentiableOn_of_localBound
    family Set.univ isOpen_univ (fun point => (holomorphic point).differentiableOn)
  intro center _
  obtain ⟨bound, nonnegative, bounds⟩ :=
    bounded (Metric.closedBall center 2) (isCompact_closedBall center 2)
  refine ⟨1, zero_lt_one, Set.subset_univ _, bound, ?_⟩
  intro parameter membership
  apply (BoundedContinuousFunction.norm_le nonnegative).mpr
  intro point
  exact bounds parameter (Metric.ball_subset_closedBall (by simpa using membership)) point

/-- Uniform bound near a point where every slice has nonnegative order. -/
theorem eventually_bounded {Space : Type} [TopologicalSpace Space]
    {family : ℂ → BoundedContinuousFunction Space ℂ} {center : ℂ}
    (meromorphic : MeromorphicAt family center)
    (pointwise : ∀ point, 0 ≤ meromorphicOrderAt (fun parameter => family parameter point) center) :
    ∃ bound : ℝ, ∀ᶠ parameter in 𝓝[≠] center, ∀ point, ‖family parameter point‖ ≤ bound :=
  BoundedMeromorphicFamily.eventually_bounded meromorphic pointwise

/-- If every slice of a meromorphic family of bounded continuous functions has nonnegative order
at `center` and converges on a punctured neighbourhood of `center`, the limit is continuous. -/
theorem limit_continuous {Space : Type} [TopologicalSpace Space]
    {family : ℂ → BoundedContinuousFunction Space ℂ} {center : ℂ}
    (meromorphic : MeromorphicAt family center)
    (pointwise : ∀ point, 0 ≤ meromorphicOrderAt (fun parameter => family parameter point) center)
    (limit : Space → ℂ)
    (tendsto : ∀ point, Tendsto (fun parameter => family parameter point) (𝓝[≠] center)
      (𝓝 (limit point))) :
    Continuous limit := by
  have analytic := meromorphic.meromorphicOrderAt_nonneg_iff_analyticAt_toMeromorphicNFAt.mp
    (BoundedMeromorphicFamily.nonnegative_order meromorphic pointwise)
  let value := toMeromorphicNFAt family center center
  have valueLimit : ∀ point, value point = limit point := by
    intro point
    have analyticLimit : Tendsto (toMeromorphicNFAt family center) (𝓝[≠] center)
        (𝓝 value) := analytic.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have evaluated : Tendsto (fun parameter => toMeromorphicNFAt family center parameter point)
        (𝓝[≠] center) (𝓝 (value point)) := by
      have composed := ((BoundedContinuousFunction.evalCLM ℂ point).continuous.tendsto
        value).comp analyticLimit
      simpa only [Function.comp_def, BoundedContinuousFunction.evalCLM_apply] using composed
    have familyLimit : Tendsto (fun parameter => family parameter point) (𝓝[≠] center)
        (𝓝 (value point)) := by
      refine evaluated.congr' ?_
      filter_upwards [meromorphic.eq_nhdsNE_toMeromorphicNFAt] with parameter equality
      rw [equality]
    exact tendsto_nhds_unique familyLimit (tendsto point)
  have equality : limit = fun point => value point := funext fun point => (valueLimit point).symm
  rw [equality]
  exact value.continuous

end TernaryPeriodPolynomials.EdgeEisenstein.CompactContinuation
