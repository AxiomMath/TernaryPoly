module

public import TernaryPeriodPolynomials.DifferentialForm.Connection.NormalizedPartition
public import TernaryPeriodPolynomials.DifferentialForm.Connection.FiniteGluing

@[expose] public section


/-! Global quantitative smooth approximation of compactly supported quotient Lipschitz scalars. -/
noncomputable section
namespace TernaryPoly.SymmetricSpaceRiemannian
open SymmetricSpaceCharts SymmetricSpaceCovering
open Manifold Bundle Filter Set Metric
open scoped ContDiff Manifold Bundle Topology NNReal
attribute [local instance] orbitMetricSpace

/-- Finite normalized charts and quantitatively chosen local errors give the actual dual bound `5K`. -/
theorem exists_global_smooth_approx {f : OrbitSpace → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (hK : HasCompactSupport f) (hKpos : 0 < K)
    {η : ℝ} (hη : 0 < η) :
    ∃ g : OrbitSpace → ℝ, ContMDiff 𝓘(ℝ, Coordinates) 𝓘(ℝ, ℝ) ∞ g ∧
      (∀ x, dist (g x) (f x) ≤ η) ∧ ∀ x, ‖scalarDifferential g x‖ ≤ 5 * (K : ℝ) := by
  classical
  obtain ⟨P⟩ := exists_finiteNormalizedPartition hK
  choose D _hDpos hD using (fun i : P.centers => (P.weight_bounds i).2)
  let B : ℝ := 1 + ∑ i : P.centers, |D i|
  have hB : 0 < B := by
    dsimp [B]
    positivity
  have hDB (i : P.centers) : D i ≤ B := by
    have h : |D i| ≤ ∑ j : P.centers, |D j| :=
      Finset.single_le_sum (fun j _ => abs_nonneg (D j)) (Finset.mem_univ i)
    exact (le_abs_self (D i)).trans (h.trans (le_add_of_nonneg_left zero_le_one))
  let N : ℝ := Fintype.card P.centers
  have hN : 0 ≤ N := by positivity
  let δ : ℝ := min η (K : ℝ) / (1 + N * B)
  have hδ : 0 < δ := div_pos (lt_min hη (by exact_mod_cast hKpos)) (by positivity)
  have hδeq : δ * (1 + N * B) = min η (K : ℝ) := by
    dsimp [δ]
    exact div_mul_cancel₀ _ (by positivity)
  have hδη : δ ≤ η := by
    have hm := min_le_left η (K : ℝ)
    nlinarith [mul_nonneg hN hB.le]
  have hδK : N * δ * B ≤ (K : ℝ) := by
    have hm := min_le_right η (K : ℝ)
    nlinarith
  have hexi (i : P.centers) := exists_normalized_smooth_approx i.val (2 * P.radius i)
    (fun v hv => let h := P.bounds i v (ball_subset_closedBall hv); ⟨h.1, h.2.2⟩) hf hδ
  choose a has hal hae using hexi
  let φ : P.centers → OrbitSpace → ℝ := fun i => P.weights i
  let u : P.centers → OrbitSpace → ℝ := fun i => a i ∘ normalizedChart i.val
  have hφ (i : P.centers) : ContMDiff 𝓘(ℝ, Coordinates) 𝓘(ℝ, ℝ) ∞ (φ i) :=
    (P.weights i).contMDiff
  have hu (i : P.centers) (y : OrbitSpace) (hy : y ∈ tsupport (φ i)) :
      ContMDiffAt 𝓘(ℝ, Coordinates) 𝓘(ℝ, ℝ) ∞ (u i) y := by
    have hys := (P.subordinate i hy).1
    exact (has i).contMDiff.contMDiffAt.comp y
      ((contMDiffOn_normalizedChart i.val).contMDiffAt ((normalizedChart i.val).open_source.mem_nhds hys))
  have herror (i : P.centers) (y : OrbitSpace) (hy : y ∈ tsupport (φ i)) : |u i y - f y| ≤ δ := by
    have hyp := P.subordinate i hy
    have hv : normalizedChart i.val y ∈ ball (normalizedChart i.val i.val) (2 * P.radius i) :=
      ball_subset_ball (by linarith [P.radius_pos i]) hyp.2
    have he := congrArg f ((normalizedChart i.val).left_inv hyp.1)
    simpa only [u, Function.comp_apply, he, Real.dist_eq] using (hae i _ hv).le
  have hgrad (i : P.centers) (y : OrbitSpace) (hy : y ∈ tsupport (φ i)) :
      ‖scalarDifferential (u i) y‖ ≤ 4 * (K : ℝ) := by
    have hyp := P.subordinate i hy
    apply norm_scalarDifferential_comp_normalizedChart_le i.val y (has i) (hal i) hyp.1
    apply norm_normalizedChartDerivative_le_on_patch i.val (P.radius i) _ y hyp
    intro v hv
    exact (P.bounds i v (ball_subset_closedBall (ball_subset_ball
      (by linarith [P.radius_pos i]) hv))).2.1.le
  have hn (i : P.centers) (x : OrbitSpace) : 0 ≤ φ i x := P.weights.nonneg i x
  have hs (x : OrbitSpace) : ∑ i, φ i x ≤ 1 := by
    simpa only [finsum_eq_sum_of_fintype] using P.weights.sum_le_one x
  have hp (x : OrbitSpace) (hx : f x ≠ 0) : ∑ i, φ i x = 1 := by
    simpa only [finsum_eq_sum_of_fintype] using P.weights.sum_eq_one (subset_closure hx)
  refine ⟨∑ i, φ i * u i, contMDiff_finite_scalar_gluing φ u hφ hu, ?_, ?_⟩
  · intro x
    rw [Real.dist_eq]
    exact (finite_scalar_gluing_error φ u f hδ.le hn hs hp herror x).trans hδη
  · intro x
    have hb := finite_scalar_gluing_differential_bound φ u f hφ hu hf.continuous
      (by positivity : 0 ≤ 4 * (K : ℝ)) hδ.le hB.le hn hs hp herror hgrad
      (fun i y => (hD i y).trans (hDB i)) x
    dsimp [N] at hδK
    exact hb.trans (by nlinarith)

end TernaryPoly.SymmetricSpaceRiemannian
