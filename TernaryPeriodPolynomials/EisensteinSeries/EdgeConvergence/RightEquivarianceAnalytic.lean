module

public import Mathlib.Analysis.Complex.AbsMax
public import Mathlib.Topology.UniformSpace.HeineCantor
public import Mathlib.Analysis.Normed.Group.Basic
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
public import Mathlib.Topology.Order.ExtrClosure
public import Mathlib.Topology.WithTopology

@[expose] public section


/-!
# A two-variable continuity lemma for the right-equivariance argument

Right real equivariance of the edge standard value is proved by comparing, for fixed `g`, the
function `A(s)` (the continuation of `J_s[F^{R(h) f}](g)`, the flat family of the translate `R(h) f`)
with `B(s)` (the continuation of `J_s[F^f](g h)`). Both are obtained from one two-variable family
`G(s, z)` (the standard integral of the flat family of `ρ_h^z · R(h) f`) by `A(s) = G(s, 0)` and
`B(s) = G(s, s - s₀)`. If `G` is holomorphic in `s` on a closed disc for every small `z`
(a removable singularity at `s₀` for each fixed `z`) and continuous on the circle `|s - s₀| = r`
jointly with `z`, then `G` is jointly continuous at `(s₀, 0)`, hence its restriction to the diagonal
`z = s - s₀` has the same value at `s₀` as the axis `z = 0`. No assumption on the order of a possible
pole of the scalar `λ̃(s)` (in `G = λ̃ · R`) is needed: only the regularity of `G(·, z)` at `s₀`
for each `z` and the continuity of `G` on a circle where `λ̃` is pole free.

The proof is the maximum modulus principle for `s ↦ G(s, z) - G(s, 0)` on the disc, plus uniform
continuity on the compact set `circle × closedBall (0, δ/2)`.
-/

open Metric Filter Topology Set

noncomputable section

namespace TernaryPeriodPolynomials.EdgeConvergence.RightEquivariance

/-- Joint continuity at `(s₀, 0)` from holomorphy in `s` on a closed disc (for each small `z`) and
joint continuity on the circle. -/
theorem continuousAt_of_boundary_control {G : ℂ → ℂ → ℂ} {s₀ : ℂ} {r δ : ℝ}
    (hr : 0 < r) (hδ : 0 < δ)
    (holo : ∀ z : ℂ, ‖z‖ < δ → DifferentiableOn ℂ (fun s => G s z) (closedBall s₀ r))
    (circle : ContinuousOn (fun p : ℂ × ℂ => G p.1 p.2) (sphere s₀ r ×ˢ ball (0 : ℂ) δ)) :
    ContinuousAt (fun p : ℂ × ℂ => G p.1 p.2) (s₀, 0) := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  have halfPositive : 0 < ε / 2 := half_pos hε
  -- uniform continuity on the compact set `circle × closedBall (0, δ/2)`
  have compactSet : IsCompact (sphere s₀ r ×ˢ closedBall (0 : ℂ) (δ / 2)) :=
    (isCompact_sphere s₀ r).prod (isCompact_closedBall 0 (δ / 2))
  have subset : sphere s₀ r ×ˢ closedBall (0 : ℂ) (δ / 2) ⊆ sphere s₀ r ×ˢ ball (0 : ℂ) δ := by
    intro p membership
    refine ⟨membership.1, ?_⟩
    rw [mem_ball_zero_iff]
    exact lt_of_le_of_lt (mem_closedBall_zero_iff.mp membership.2) (by linarith)
  have uniform := compactSet.uniformContinuousOn_of_continuous (circle.mono subset)
  rw [Metric.uniformContinuousOn_iff] at uniform
  obtain ⟨η, ηPositive, ηProperty⟩ := uniform (ε / 2) halfPositive
  -- continuity of the axis at `s₀`
  have axis : ContinuousAt (fun s => G s 0) s₀ :=
    ((holo 0 (by simpa using hδ)).continuousOn).continuousAt (closedBall_mem_nhds s₀ hr)
  obtain ⟨θ, θPositive, θProperty⟩ := Metric.continuousAt_iff.mp axis (ε / 2) halfPositive
  refine ⟨min (min η (δ / 2)) (min θ r), lt_min (lt_min ηPositive (by linarith))
    (lt_min θPositive hr), ?_⟩
  rintro ⟨s, z⟩ close
  rw [Prod.dist_eq, max_lt_iff] at close
  obtain ⟨closeS, closeZ⟩ := close
  have closeS' : dist s s₀ < min θ r := lt_of_lt_of_le closeS (min_le_right _ _)
  have closeZ' : dist z 0 < min η (δ / 2) := lt_of_lt_of_le closeZ (min_le_left _ _)
  have sTheta : dist s s₀ < θ := lt_of_lt_of_le closeS' (min_le_left _ _)
  have sRadius : dist s s₀ < r := lt_of_lt_of_le closeS' (min_le_right _ _)
  have zEta : ‖z‖ < η := by
    rw [← dist_zero_right]
    exact lt_of_lt_of_le closeZ' (min_le_left _ _)
  have zHalf : ‖z‖ < δ / 2 := by
    rw [← dist_zero_right]
    exact lt_of_lt_of_le closeZ' (min_le_right _ _)
  -- the difference `G · z - G · 0` is holomorphic on the closed disc and small on the circle
  have difference : DiffContOnCl ℂ (fun t => G t z - G t 0) (ball s₀ r) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball s₀ hr.ne']
    exact (holo z (by linarith)).sub (holo 0 (by simpa using hδ))
  have onCircle : ∀ t ∈ frontier (ball s₀ r), ‖G t z - G t 0‖ ≤ ε / 2 := by
    intro t membership
    rw [frontier_ball s₀ hr.ne'] at membership
    have first : (t, z) ∈ sphere s₀ r ×ˢ closedBall (0 : ℂ) (δ / 2) :=
      ⟨membership, mem_closedBall_zero_iff.mpr zHalf.le⟩
    have second : (t, (0 : ℂ)) ∈ sphere s₀ r ×ˢ closedBall (0 : ℂ) (δ / 2) :=
      ⟨membership, mem_closedBall_self (by linarith)⟩
    have near : dist (t, z) (t, (0 : ℂ)) < η := by
      rw [Prod.dist_eq]
      simp only [dist_self, dist_zero_right]
      exact max_lt ηPositive zEta
    have bound := ηProperty _ first _ second near
    rw [dist_eq_norm] at bound
    exact bound.le
  have inside : ‖G s z - G s 0‖ ≤ ε / 2 :=
    Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball difference onCircle
      (subset_closure (mem_ball.mpr sRadius))
  have axisBound : dist (G s 0) (G s₀ 0) < ε / 2 := θProperty sTheta
  calc dist (G s z) (G s₀ 0) ≤ dist (G s z) (G s 0) + dist (G s 0) (G s₀ 0) := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := by
        have : dist (G s z) (G s 0) ≤ ε / 2 := by rw [dist_eq_norm]; exact inside
        linarith
    _ = ε := by ring

/-- The diagonal `z = s - s₀` and the axis `z = 0` have the same limit at `s₀`. -/
theorem tendsto_diagonal {G : ℂ → ℂ → ℂ} {s₀ : ℂ} {r δ : ℝ}
    (hr : 0 < r) (hδ : 0 < δ)
    (holo : ∀ z : ℂ, ‖z‖ < δ → DifferentiableOn ℂ (fun s => G s z) (closedBall s₀ r))
    (circle : ContinuousOn (fun p : ℂ × ℂ => G p.1 p.2) (sphere s₀ r ×ˢ ball (0 : ℂ) δ)) :
    Tendsto (fun s => G s (s - s₀)) (𝓝 s₀) (𝓝 (G s₀ 0)) := by
  have joint := continuousAt_of_boundary_control hr hδ holo circle
  have pathContinuous : Continuous (fun s : ℂ => (s, s - s₀)) :=
    continuous_id.prodMk (continuous_id.sub continuous_const)
  have atPoint : (fun s : ℂ => (s, s - s₀)) s₀ = (s₀, 0) := by simp
  have composed : ContinuousAt ((fun p : ℂ × ℂ => G p.1 p.2) ∘ (fun s : ℂ => (s, s - s₀))) s₀ :=
    ContinuousAt.comp_of_eq joint pathContinuous.continuousAt atPoint
  have tendsto := composed.tendsto
  simpa [Function.comp_def, atPoint] using tendsto

/-- If a continuous function `B` agrees with the diagonal of `G` near (but not at) `s₀`, and `A`
agrees with the axis value of `G` at `s₀`, then `A s₀ = B s₀`. -/
theorem eq_of_axis_diagonal {G : ℂ → ℂ → ℂ} {s₀ : ℂ} {r δ : ℝ}
    (hr : 0 < r) (hδ : 0 < δ)
    (holo : ∀ z : ℂ, ‖z‖ < δ → DifferentiableOn ℂ (fun s => G s z) (closedBall s₀ r))
    (circle : ContinuousOn (fun p : ℂ × ℂ => G p.1 p.2) (sphere s₀ r ×ˢ ball (0 : ℂ) δ))
    {A B : ℂ → ℂ} (axis : A s₀ = G s₀ 0) (continuousB : ContinuousAt B s₀)
    (diagonal : ∀ᶠ s in 𝓝[≠] s₀, B s = G s (s - s₀)) :
    A s₀ = B s₀ := by
  have toDiagonal := (tendsto_diagonal hr hδ holo circle).mono_left (nhdsWithin_le_nhds (s := {s₀}ᶜ))
  have toB : Tendsto B (𝓝[≠] s₀) (𝓝 (B s₀)) := continuousB.tendsto.mono_left nhdsWithin_le_nhds
  have viaDiagonal : Tendsto B (𝓝[≠] s₀) (𝓝 (G s₀ 0)) :=
    toDiagonal.congr' (diagonal.mono fun s h => h.symm)
  rw [axis]
  exact tendsto_nhds_unique viaDiagonal toB

end TernaryPeriodPolynomials.EdgeConvergence.RightEquivariance
