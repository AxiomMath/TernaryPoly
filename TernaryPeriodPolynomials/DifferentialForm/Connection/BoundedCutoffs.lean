module

public import TernaryPeriodPolynomials.DifferentialForm.Connection.Cutoff.Plateau
public import TernaryPeriodPolynomials.DifferentialForm.Connection.MetricCutoff

@[expose] public section

/-! Genuine compact smooth quotient cutoffs with uniformly vanishing actual Riemannian gradient. -/
noncomputable section
namespace TernaryPoly.SymmetricSpaceRiemannian
open SymmetricSpaceCharts SymmetricSpaceCovering
open Manifold Bundle Filter Set Metric
open scoped ContDiff Manifold Bundle Topology NNReal
attribute [local instance] orbitMetricSpace

/-- A genuine cutoff sequence on the existing quotient and its actual Riemannian tangent norms. -/
structure BoundedCutoffSequence where
  toFun : ℕ → OrbitSpace → ℝ
  bound : ℝ
  bound_pos : 0 < bound
  smooth : ∀ j, ContMDiff 𝓘(ℝ, Coordinates) 𝓘(ℝ, ℝ) ∞ (toFun j)
  compact : ∀ j, HasCompactSupport (toFun j)
  range : ∀ j q, toFun j q ∈ Icc (0 : ℝ) 1
  differential_bound : ∀ j q, ‖scalarDifferential (toFun j) q‖ ≤ bound / ((j : ℝ) + 1)
  eventually_one : ∀ K : Set OrbitSpace, IsCompact K →
    ∀ᶠ j : ℕ in atTop, ∀ q ∈ K, toFun j q = 1

/-- The actual complete quotient geometry produces smooth compact cutoffs, with no smoothing premise. -/
theorem exists_boundedCutoffSequence (q₀ : OrbitSpace) : Nonempty BoundedCutoffSequence := by
  classical
  let : ProperSpace OrbitSpace := orbit_proper
  let r (j : ℕ) : ℝ := (j : ℝ) + 1
  have hr (j : ℕ) : 0 < r j := by dsimp [r]; positivity
  let slope (j : ℕ) : ℝ≥0 := ⟨(r j)⁻¹, inv_nonneg.mpr (hr j).le⟩
  let f (j : ℕ) := PolynomialFormConnection.metricCutoff q₀ (r j)
  have hf (j : ℕ) : LipschitzWith (slope j) (f j) :=
    PolynomialFormConnection.lipschitzWith_metricCutoff q₀ (hr j)
  have hfc (j : ℕ) : HasCompactSupport (f j) :=
    PolynomialFormConnection.metricCutoff_hasCompactSupport q₀ (hr j)
  have hex (j : ℕ) := exists_global_smooth_approx (hf j) (hfc j)
    (show 0 < slope j from inv_pos.mpr (hr j)) (show (0 : ℝ) < 1 / 8 by norm_num)
  choose g hgs hge hgd using hex
  obtain ⟨A, hA, hAb⟩ := exists_cutoffPlateau_derivative_bound
  have hp (j : ℕ) := cutoffPlateau_comp_properties (f j) (g j) (hfc j) (hgs j) (hge j)
  refine ⟨{
    toFun := fun j => cutoffPlateau ∘ g j
    bound := 5 * A
    bound_pos := by positivity
    smooth := fun j => (hp j).1
    compact := fun j => (hp j).2.1
    range := fun j => (hp j).2.2.1
    differential_bound := ?_
    eventually_one := ?_
  }⟩
  · intro j q
    have hb := norm_scalarDifferential_cutoffPlateau_le (g j) (hgs j) hA.le hAb (hgd j) q
    apply hb.trans_eq
    change A * (5 * (r j)⁻¹) = 5 * A / ((j : ℝ) + 1)
    dsimp [r]
    ring
  · intro K hK
    filter_upwards [PolynomialFormConnection.metricCutoff_eventually_one_on_compact q₀ hK] with j hj
    intro q hq
    exact (hp j).2.2.2 q (hj q hq)

/-- A fixed open neighborhood of each point lies in the plateau of every sufficiently late cutoff. -/
theorem BoundedCutoffSequence.locally_eventually_one (c : BoundedCutoffSequence) (q : OrbitSpace) :
    ∃ U : Set OrbitSpace, IsOpen U ∧ q ∈ U ∧
      ∀ᶠ j : ℕ in atTop, EqOn (c.toFun j) (fun _ => (1 : ℝ)) U := by
  let : ProperSpace OrbitSpace := orbit_proper
  refine ⟨ball q 1, isOpen_ball, mem_ball_self zero_lt_one, ?_⟩
  filter_upwards [c.eventually_one (closedBall q 1) (isCompact_closedBall q 1)] with j hj
  exact fun y hy => hj y (ball_subset_closedBall hy)

/-- The bound is explicitly a bound on evaluation against every actual Riemannian tangent vector. -/
theorem BoundedCutoffSequence.apply_bound (c : BoundedCutoffSequence) (j : ℕ) (q : OrbitSpace)
    (v : TangentSpace 𝓘(ℝ, Coordinates) q) :
    |scalarDifferential (c.toFun j) q v| ≤ c.bound / ((j : ℝ) + 1) * ‖v‖ := by
  have h := (scalarDifferential (c.toFun j) q).le_opNorm v
  rw [Real.norm_eq_abs] at h
  exact h.trans (mul_le_mul_of_nonneg_right (c.differential_bound j q) (norm_nonneg v))

/-- In particular, the smooth cutoff values converge pointwise to one. -/
theorem BoundedCutoffSequence.tendsto_one (c : BoundedCutoffSequence) (q : OrbitSpace) :
    Tendsto (fun j => c.toFun j q) atTop (𝓝 (1 : ℝ)) := by
  have he : (fun j => c.toFun j q) =ᶠ[atTop] (fun _ => (1 : ℝ)) := by
    filter_upwards [c.eventually_one {q} isCompact_singleton] with j hj
    exact hj q (mem_singleton q)
  exact tendsto_const_nhds.congr' he.symm

/-- The estimate uses the quotient metric tensor itself, making its normalization explicit. -/
theorem BoundedCutoffSequence.inner_bound (c : BoundedCutoffSequence) (j : ℕ) (q : OrbitSpace)
    (v : TangentSpace 𝓘(ℝ, Coordinates) q) :
    |scalarDifferential (c.toFun j) q v| ≤ c.bound / ((j : ℝ) + 1) *
      Real.sqrt (SymmetricSpaceTraceMetric.orbitInner q v v) := by
  have hn : ‖v‖ = Real.sqrt (SymmetricSpaceTraceMetric.orbitInner q v v) := by
    rw [norm_eq_sqrt_real_inner]
    rfl
  rw [← hn]
  exact c.apply_bound j q v

/-- The existing quotient has an unconditional bounded-gradient compact cutoff sequence. -/
theorem nonempty_boundedCutoffSequence : Nonempty BoundedCutoffSequence :=
  exists_boundedCutoffSequence (Classical.choice inferInstance)

/-- A fixed choice of the quotient cutoff sequence. -/
def boundedCutoffSequence : BoundedCutoffSequence := Classical.choice nonempty_boundedCutoffSequence

end TernaryPoly.SymmetricSpaceRiemannian
