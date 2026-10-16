module

public import Mathlib
public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.EndpointLift

@[expose] public section


/-!
# The Cauchy circle value of a factorized function

Original work by Claude Sonnet 5.5.

If `G` is analytic at `c`, `lam` is analytic on a punctured disc, `Rs` is holomorphic on a closed
disc and `G = lam * Rs` on a punctured neighbourhood of `c`, then for every radius `ρ` in the disc
of analyticity of `lam`, the circle average
`(2πi)⁻¹ ∮_{|s-c|=ρ} (s-c)⁻¹ • (lam s • Rs s) ds` equals `G c`. The radius need not be small
relative to the neighbourhood of the factorization: the annulus theorem moves the circle inside
the neighbourhood where `G = lam * Rs`.
-/

open Metric Filter Topology

namespace TernaryPeriodPolynomials.EdgeConvergence

namespace EdgeCircle

/-- **Circle value of a factorization.** -/
theorem circleAverage_eq_value {c : ℂ} {radius epsilon : ℝ} (radius_pos : 0 < radius)
    (radius_lt : radius < epsilon) {lam Rs G : ℂ → ℂ}
    (lam_analytic : ∀ s : ℂ, s ≠ c → dist s c < epsilon → AnalyticAt ℂ lam s)
    (Rs_differentiable : DifferentiableOn ℂ Rs (closedBall c radius))
    (G_analytic : AnalyticAt ℂ G c)
    (factorization : ∀ᶠ s in 𝓝[≠] c, G s = lam s * Rs s) :
    (2 * (Real.pi : ℂ) * Complex.I)⁻¹ •
        ∮ s in C(c, radius), (s - c)⁻¹ • (lam s • Rs s) = G c := by
  obtain ⟨delta₁, delta₁_pos, analytic_near⟩ :=
    Metric.eventually_nhds_iff.1 G_analytic.eventually_analyticAt
  obtain ⟨delta₂, delta₂_pos, factor_near⟩ :=
    LambdaContinuation.exists_punctured_ball factorization
  set small : ℝ := min (min delta₁ delta₂) radius / 2 with small_def
  have min_pos : 0 < min (min delta₁ delta₂) radius :=
    lt_min (lt_min delta₁_pos delta₂_pos) radius_pos
  have small_pos : 0 < small := by
    rw [small_def]
    exact half_pos min_pos
  have small_lt_min : small < min (min delta₁ delta₂) radius := by
    rw [small_def]
    exact half_lt_self min_pos
  have small_lt_delta₁ : small < delta₁ :=
    lt_of_lt_of_le small_lt_min ((min_le_left _ _).trans (min_le_left _ _))
  have small_lt_delta₂ : small < delta₂ :=
    lt_of_lt_of_le small_lt_min ((min_le_left _ _).trans (min_le_right _ _))
  have small_lt_radius : small < radius := lt_of_lt_of_le small_lt_min (min_le_right _ _)
  have inverse_continuous : ContinuousOn (fun s : ℂ => (s - c)⁻¹) (closedBall c radius \ ball c small) := by
    refine (continuousOn_id.sub continuousOn_const).inv₀ (fun s membership => ?_)
    intro equal
    have same : s = c := sub_eq_zero.1 equal
    have notBall : ¬ dist s c < small := membership.2
    rw [same, dist_self] at notBall
    exact notBall small_pos
  have lam_continuous : ContinuousOn lam (closedBall c radius \ ball c small) := by
    intro s membership
    have notBall : ¬ dist s c < small := membership.2
    have different : s ≠ c := by
      intro same
      rw [same, dist_self] at notBall
      exact notBall small_pos
    have inside : dist s c < epsilon :=
      lt_of_le_of_lt (mem_closedBall.1 membership.1) radius_lt
    exact (lam_analytic s different inside).continuousAt.continuousWithinAt
  have integrand_continuous : ContinuousOn (fun s : ℂ => (s - c)⁻¹ • (lam s • Rs s))
      (closedBall c radius \ ball c small) :=
    inverse_continuous.smul (lam_continuous.smul
      (Rs_differentiable.continuousOn.mono Set.sdiff_subset))
  have annulus : (∮ s in C(c, radius), (s - c)⁻¹ • (lam s • Rs s)) =
      ∮ s in C(c, small), (s - c)⁻¹ • (lam s • Rs s) := by
    refine Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable small_pos
      small_lt_radius.le Set.countable_empty integrand_continuous ?_
    intro s membership
    have notClosed : ¬ s ∈ closedBall c small := membership.1.2
    have inBall : s ∈ ball c radius := membership.1.1
    have different : s ≠ c := by
      intro same
      apply notClosed
      rw [same]
      exact mem_closedBall_self small_pos.le
    have inside : dist s c < epsilon := lt_trans (mem_ball.1 inBall) radius_lt
    have inverse_differentiable : DifferentiableAt ℂ (fun s : ℂ => (s - c)⁻¹) s :=
      (differentiableAt_id.sub_const c).inv (sub_ne_zero.2 different)
    have lam_differentiable : DifferentiableAt ℂ lam s :=
      (lam_analytic s different inside).differentiableAt
    have Rs_differentiableAt : DifferentiableAt ℂ Rs s :=
      (Rs_differentiable s (ball_subset_closedBall inBall)).differentiableAt
        (Filter.mem_of_superset (isOpen_ball.mem_nhds inBall) ball_subset_closedBall)
    exact inverse_differentiable.smul (lam_differentiable.smul Rs_differentiableAt)
  have on_circle : (∮ s in C(c, small), (s - c)⁻¹ • (lam s • Rs s)) =
      ∮ s in C(c, small), (s - c)⁻¹ • G s := by
    refine circleIntegral.integral_congr small_pos.le (fun s membership => ?_)
    have onSphere : dist s c = small := mem_sphere.1 membership
    have different : s ≠ c := by
      intro same
      rw [same, dist_self] at onSphere
      exact small_pos.ne onSphere
    have equation : G s = lam s * Rs s :=
      factor_near s different (by rw [onSphere]; exact small_lt_delta₂)
    simp only [equation, smul_eq_mul]
  have G_differentiable : DifferentiableOn ℂ G (closedBall c small) := by
    intro s membership
    have inside : dist s c < delta₁ := lt_of_le_of_lt (mem_closedBall.1 membership) small_lt_delta₁
    exact (analytic_near inside).differentiableAt.differentiableWithinAt
  rw [annulus, on_circle, G_differentiable.circleIntegral_sub_inv_smul (mem_ball_self small_pos),
    inv_smul_smul₀ EndpointLift.two_pi_I_ne_zero]

end EdgeCircle

end TernaryPeriodPolynomials.EdgeConvergence
