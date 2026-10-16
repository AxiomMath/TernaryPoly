module

public import Mathlib
public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.LambdaContinuation

@[expose] public section


/-!
# The endpoint lift by a Cauchy integral

Given a vector-valued function `R : ℂ → E` into a complex Banach space, continuous on a circle of
radius `r` about `c`, and a scalar function `lam` continuous on the circle (the continued
multiplier, analytic off its pole at `c`), the endpoint lift is
`(2πi)⁻¹ ∮_{|s-c|=r} (s-c)⁻¹ • (lam s • R s) ds`.

Continuous linear maps commute with the circle integral, so if a continuous linear functional `ℓ`
realizes `R s` as the scalar `Rs s` and `J = lam * Rs` on the circle with `J` holomorphic on the
closed disc, then `ℓ` of the lift is the value `J c` (a removable singularity at `c`).
-/

open Metric Filter Topology

namespace TernaryPeriodPolynomials.EdgeConvergence

namespace EndpointLift

section Lift

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- The endpoint lift: the Cauchy integral `(2πi)⁻¹ ∮_{|s-c|=r} (s-c)⁻¹ • (lam s • R s) ds`. -/
noncomputable def endpointLift (c : ℂ) (r : ℝ) (lam : ℂ → ℂ) (R : ℂ → E) : E :=
  (2 * (Real.pi : ℂ) * Complex.I)⁻¹ • ∮ s in C(c, r), (s - c)⁻¹ • (lam s • R s)

theorem sub_center_ne_zero {c s : ℂ} {r : ℝ} (hr : 0 < r) (hs : s ∈ sphere c r) : s - c ≠ 0 := by
  intro h
  have h' : s = c := sub_eq_zero.1 h
  have hd : dist s c = r := mem_sphere.1 hs
  rw [h', dist_self] at hd
  exact hr.ne hd

omit [CompleteSpace E] in
/-- The integrand of the endpoint lift is circle integrable. -/
theorem circleIntegrable_integrand {c : ℂ} {r : ℝ} (hr : 0 < r) {lam : ℂ → ℂ} {R : ℂ → E}
    (hlam : ContinuousOn lam (sphere c r)) (hR : ContinuousOn R (sphere c r)) :
    CircleIntegrable (fun s => (s - c)⁻¹ • (lam s • R s)) c r := by
  apply ContinuousOn.circleIntegrable hr.le
  have h1 : ContinuousOn (fun s : ℂ => (s - c)⁻¹) (sphere c r) :=
    (continuousOn_id.sub continuousOn_const).inv₀ (fun s hs => sub_center_ne_zero hr hs)
  exact h1.smul (hlam.smul hR)

/-- A continuous `ℂ`-linear map commutes with the circle integral. -/
theorem circleIntegral_clm_comm {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F]
    (ℓ : E →L[ℂ] F) {f : ℂ → E} {c : ℂ} {r : ℝ} (hf : CircleIntegrable f c r) :
    ℓ (∮ z in C(c, r), f z) = ∮ z in C(c, r), ℓ (f z) := by
  have h := ℓ.intervalIntegral_comp_comm hf.out
  unfold circleIntegral
  rw [← h]
  refine intervalIntegral.integral_congr (fun θ _ => ?_)
  simp only [map_smul]

/-- A continuous linear map applied to the endpoint lift is the endpoint lift of the image. -/
theorem map_endpointLift {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (ℓ : E →L[ℂ] F)
    {c : ℂ} {r : ℝ} (hr : 0 < r) {lam : ℂ → ℂ} {R : ℂ → E}
    (hlam : ContinuousOn lam (sphere c r)) (hR : ContinuousOn R (sphere c r)) :
    ℓ (endpointLift c r lam R) =
      (2 * (Real.pi : ℂ) * Complex.I)⁻¹ • ∮ s in C(c, r), (s - c)⁻¹ • (lam s • ℓ (R s)) := by
  unfold endpointLift
  rw [map_smul, circleIntegral_clm_comm ℓ (circleIntegrable_integrand hr hlam hR)]
  simp only [map_smul]

theorem two_pi_I_ne_zero : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 :=
  mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.2 Real.pi_ne_zero))
    Complex.I_ne_zero

/-- **Realization of the endpoint lift.** If a continuous linear functional `ℓ` takes `R s` to the
scalar `Rs s` on the circle, `lam` and `R` are continuous on the circle, `J` is holomorphic on the
closed disc and `J = lam * Rs` on the circle, then `ℓ` of the endpoint lift is `J c`. -/
theorem realize_endpointLift {c : ℂ} {r : ℝ} (hr : 0 < r) {lam : ℂ → ℂ} {R : ℂ → E}
    {Rs J : ℂ → ℂ} (ℓ : E →L[ℂ] ℂ)
    (hlam : ContinuousOn lam (sphere c r)) (hR : ContinuousOn R (sphere c r))
    (hℓ : ∀ s ∈ sphere c r, ℓ (R s) = Rs s)
    (hJ : DifferentiableOn ℂ J (closedBall c r))
    (hfac : ∀ s ∈ sphere c r, J s = lam s * Rs s) :
    ℓ (endpointLift c r lam R) = J c := by
  rw [map_endpointLift ℓ hr hlam hR]
  have hcongr : (∮ s in C(c, r), (s - c)⁻¹ • (lam s • ℓ (R s))) =
      ∮ s in C(c, r), (s - c)⁻¹ • J s := by
    refine circleIntegral.integral_congr hr.le (fun s hs => ?_)
    simp only [hℓ s hs, hfac s hs, smul_eq_mul]
  rw [hcongr, hJ.circleIntegral_sub_inv_smul (mem_ball_self hr), inv_smul_smul₀ two_pi_I_ne_zero]

omit [CompleteSpace E] in
/-- The endpoint lift is the circle average of `lam • R`. -/
theorem endpointLift_eq_circleAverage {c : ℂ} {r : ℝ} (hr : 0 < r) (lam : ℂ → ℂ) (R : ℂ → E) :
    endpointLift c r lam R = Real.circleAverage (fun s => lam s • R s) c r := by
  have key : ∀ θ : ℝ, deriv (circleMap c r) θ •
      ((circleMap c r θ - c)⁻¹ • (lam (circleMap c r θ) • R (circleMap c r θ))) =
        Complex.I • (lam (circleMap c r θ) • R (circleMap c r θ)) := by
    intro θ
    rw [deriv_circleMap, smul_smul (circleMap 0 r θ * Complex.I)]
    congr 1
    have h0 : circleMap 0 r θ ≠ 0 := circleMap_ne_center hr.ne'
    rw [circleMap_sub_center, mul_comm (circleMap 0 r θ) Complex.I, mul_assoc,
      mul_inv_cancel₀ h0, mul_one]
  have hint : (∮ s in C(c, r), (s - c)⁻¹ • (lam s • R s)) =
      Complex.I • ∫ θ in (0 : ℝ)..2 * Real.pi, lam (circleMap c r θ) • R (circleMap c r θ) := by
    unfold circleIntegral
    rw [← intervalIntegral.integral_smul]
    exact intervalIntegral.integral_congr (fun θ _ => key θ)
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  have hscalar : (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * Complex.I = (((2 * Real.pi)⁻¹ : ℝ) : ℂ) := by
    push_cast
    field_simp
  unfold endpointLift
  rw [hint, smul_smul, hscalar, Real.circleAverage_def]
  exact Complex.coe_smul _ _

end Lift

section CircleData

/-- Data on a small circle for the Cauchy lift: if `J` is analytic at `s₀`, `lam` is meromorphic
at `s₀`, and `J = lam * Rs` in a punctured neighbourhood of `s₀`, then for every small enough
radius `r`, `J` is holomorphic on the closed disc, `lam` is analytic (hence continuous) on the
circle, and `J = lam * Rs` on the circle. -/
theorem exists_circle_data {J lam Rs : ℂ → ℂ} {s₀ : ℂ} (hJ : AnalyticAt ℂ J s₀)
    (hlam : MeromorphicAt lam s₀) (hfac : ∀ᶠ s in 𝓝[≠] s₀, J s = lam s * Rs s) :
    ∃ ε > 0, ∀ r : ℝ, 0 < r → r < ε →
      DifferentiableOn ℂ J (closedBall s₀ r) ∧ (∀ s ∈ sphere s₀ r, AnalyticAt ℂ lam s) ∧
        ContinuousOn lam (sphere s₀ r) ∧ ∀ s ∈ sphere s₀ r, J s = lam s * Rs s := by
  obtain ⟨ε₁, hε₁, h₁⟩ := Metric.eventually_nhds_iff.1 hJ.eventually_analyticAt
  have h2 : ∀ᶠ s in 𝓝[≠] s₀, AnalyticAt ℂ lam s ∧ J s = lam s * Rs s :=
    hlam.eventually_analyticAt.and hfac
  obtain ⟨ε₂, hε₂, h₂⟩ := LambdaContinuation.exists_punctured_ball h2
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, fun r hr hrε => ?_⟩
  have hr1 : r < ε₁ := lt_of_lt_of_le hrε (min_le_left _ _)
  have hr2 : r < ε₂ := lt_of_lt_of_le hrε (min_le_right _ _)
  have hsph : ∀ s ∈ sphere s₀ r, AnalyticAt ℂ lam s ∧ J s = lam s * Rs s := by
    intro s hs
    have hd : dist s s₀ = r := mem_sphere.1 hs
    have hne : s ≠ s₀ := by
      intro h
      rw [h, dist_self] at hd
      exact hr.ne hd
    exact h₂ s hne (by rw [hd]; exact hr2)
  refine ⟨?_, fun s hs => (hsph s hs).1, ?_, fun s hs => (hsph s hs).2⟩
  · intro s hs
    exact (h₁ (lt_of_le_of_lt (mem_closedBall.1 hs) hr1)).differentiableAt.differentiableWithinAt
  · intro s hs
    exact (hsph s hs).1.continuousAt.continuousWithinAt

end CircleData

end EndpointLift

end TernaryPeriodPolynomials.EdgeConvergence
