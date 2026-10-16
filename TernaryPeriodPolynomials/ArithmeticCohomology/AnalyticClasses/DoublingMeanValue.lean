module

public import Mathlib

@[expose] public section


/-!
# Radial integrals and the angle-doubling mean value identity on `ℝ × ℝ`

This file proves two integral identities on the plane `ℝ × ℝ` with Lebesgue measure.

* `integral_one_add_sq_rpow_neg`: for `a > 1`, the function `(1 + s ^ 2 + t ^ 2) ^ (-a)` is
  integrable and its integral is `π / (a - 1)`.
* `integral_radial_smul_doubling_holomorphic`: if `F` is holomorphic on the unit disc, then the
  integral of a radial weight `φ (√(s ^ 2 + t ^ 2))` against `F (w (s, t))`, where
  `w (s, t) = -ψ (√(s ^ 2 + t ^ 2)) * (s - t i) ^ 2 / (s ^ 2 + t ^ 2)` runs twice around the circle
  of radius `ψ r < 1`, equals `F 0` times the integral of the weight.
  `integral_radial_mul_doubling_holomorphic` is the scalar-valued version.

Both are proved in polar coordinates; the second uses the mean value property of holomorphic
functions on each circle.
-/

open MeasureTheory Set Filter Topology Complex
open scoped Real

namespace TernaryPeriodPolynomials.AnalyticClasses

/-- Integrability on `ℝ × ℝ` is equivalent to integrability of the polar-coordinate integrand
`r • f (r cos θ, r sin θ)` on the polar target. -/
theorem integrable_iff_integrableOn_polarCoord {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : ℝ × ℝ → E) :
    Integrable f ↔ IntegrableOn (fun p => p.1 • f (polarCoord.symm p)) polarCoord.target := by
  have h1 : Integrable f ↔ IntegrableOn f polarCoord.source :=
    ⟨fun h => h.integrableOn, fun h => by
      rw [← integrableOn_univ]; exact h.congr_set_ae polarCoord_source_ae_eq_univ.symm⟩
  rw [h1, ← polarCoord.symm_image_target_eq_source,
    integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume
      polarCoord.open_target.measurableSet
      (fun p _ => (hasFDerivAt_polarCoord_symm p).hasFDerivWithinAt) polarCoord.symm.injOn f]
  refine integrableOn_congr_fun (fun p hp => ?_) polarCoord.open_target.measurableSet
  rw [polarCoord_target] at hp
  simp [det_fderivPolarCoordSymm, abs_of_pos (show (0 : ℝ) < p.1 from hp.1)]

/-- Lebesgue measure restricted to the polar target is the product of the restrictions. -/
theorem volume_restrict_polarCoord_target :
    (volume : Measure (ℝ × ℝ)).restrict polarCoord.target =
      (volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioo (-π) π)) := by
  rw [polarCoord_target, Measure.prod_restrict, Measure.volume_eq_prod]

/-- An integrable function on `ℝ × ℝ` has integral equal to the iterated polar integral. -/
theorem integral_eq_iterated_polar {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ × ℝ → E) (hf : Integrable f) :
    ∫ u, f u = ∫ r in Ioi (0 : ℝ), ∫ θ in Ioo (-π) π, r • f (polarCoord.symm (r, θ)) := by
  have hint := (integrable_iff_integrableOn_polarCoord f).1 hf
  rw [IntegrableOn, volume_restrict_polarCoord_target] at hint
  rw [← integral_comp_polarCoord_symm, volume_restrict_polarCoord_target, integral_prod _ hint]

/-- The squared Euclidean norm of `polarCoord.symm (r, θ)` is `r ^ 2`. -/
theorem polarCoord_symm_sq_add_sq (p : ℝ × ℝ) :
    (polarCoord.symm p).1 ^ 2 + (polarCoord.symm p).2 ^ 2 = p.1 ^ 2 := by
  simp only [polarCoord_symm_apply, mul_pow, ← mul_add, Real.cos_sq_add_sin_sq, mul_one]

/-- The antiderivative data for `r * (1 + r ^ 2) ^ (-a)` on `[0, ∞)`. -/
theorem radial_antideriv {a : ℝ} (ha : 1 < a) :
    (∀ x ∈ Ici (0 : ℝ), HasDerivAt (fun r : ℝ => -(1 + r ^ 2) ^ (-(a - 1)) / (2 * (a - 1)))
      (x * (1 + x ^ 2) ^ (-a)) x) ∧
    (∀ x ∈ Ioi (0 : ℝ), 0 ≤ x * (1 + x ^ 2) ^ (-a)) ∧
    Tendsto (fun r : ℝ => -(1 + r ^ 2) ^ (-(a - 1)) / (2 * (a - 1))) atTop (𝓝 0) := by
  have ha' : 0 < a - 1 := by linarith
  refine ⟨fun x _ => ?_, fun x hx => ?_, ?_⟩
  · have hpos : 0 < 1 + x ^ 2 := by positivity
    have h1 : HasDerivAt (fun r : ℝ => 1 + r ^ 2) (2 * x) x := by
      simpa using ((hasDerivAt_pow 2 x).const_add 1)
    have h2 : HasDerivAt (fun r : ℝ => -(1 + r ^ 2) ^ (-(a - 1)) / (2 * (a - 1))) _ x :=
      (h1.rpow_const (p := -(a - 1)) (Or.inl hpos.ne')).neg.div_const (2 * (a - 1))
    convert h2 using 1
    rw [show -(a - 1) - 1 = -a by ring]
    field_simp
  · have : 0 < 1 + x ^ 2 := by positivity
    exact mul_nonneg (le_of_lt hx) (Real.rpow_nonneg this.le _)
  · have h : Tendsto (fun r : ℝ => 1 + r ^ 2) atTop atTop :=
      tendsto_atTop_add_const_left _ _ (tendsto_pow_atTop two_ne_zero)
    have := ((tendsto_rpow_neg_atTop ha').comp h).neg.div_const (2 * (a - 1))
    simpa using this

/-- For `a > 1`, `∫_{(0,∞)} r (1 + r²)^(-a) dr = 1 / (2 (a - 1))`. -/
theorem integral_Ioi_mul_one_add_sq_rpow_neg {a : ℝ} (ha : 1 < a) :
    ∫ r in Ioi (0 : ℝ), r * (1 + r ^ 2) ^ (-a) = 1 / (2 * (a - 1)) := by
  obtain ⟨h1, h2, h3⟩ := radial_antideriv ha
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' h1 h2 h3]
  have : a - 1 ≠ 0 := by linarith
  field_simp
  simp

/-- For `a > 1`, `r (1 + r²)^(-a)` is integrable on `(0, ∞)`. -/
theorem integrableOn_Ioi_mul_one_add_sq_rpow_neg {a : ℝ} (ha : 1 < a) :
    IntegrableOn (fun r : ℝ => r * (1 + r ^ 2) ^ (-a)) (Ioi 0) := by
  obtain ⟨h1, h2, h3⟩ := radial_antideriv ha
  exact integrableOn_Ioi_deriv_of_nonneg' h1 h2 h3

/-- **Radial mass.** For `a > 1`, `(1 + s² + t²)^(-a)` is integrable on `ℝ × ℝ` with integral
`π / (a - 1)`. -/
theorem integral_one_add_sq_rpow_neg {a : ℝ} (ha : 1 < a) :
    Integrable (fun u : ℝ × ℝ => (1 + u.1 ^ 2 + u.2 ^ 2) ^ (-a)) ∧
      ∫ u : ℝ × ℝ, (1 + u.1 ^ 2 + u.2 ^ 2) ^ (-a) = π / (a - 1) := by
  have heq : EqOn (fun p : ℝ × ℝ => p.1 • (1 + (polarCoord.symm p).1 ^ 2 +
      (polarCoord.symm p).2 ^ 2) ^ (-a)) (fun p => p.1 * (1 + p.1 ^ 2) ^ (-a) * 1)
      polarCoord.target := by
    intro p _
    simp only [smul_eq_mul, add_assoc, polarCoord_symm_sq_add_sq, mul_one]
  constructor
  · rw [integrable_iff_integrableOn_polarCoord,
      integrableOn_congr_fun heq polarCoord.open_target.measurableSet, IntegrableOn,
      volume_restrict_polarCoord_target]
    exact (integrableOn_Ioi_mul_one_add_sq_rpow_neg ha).mul_prod (integrable_const _)
  · rw [← integral_comp_polarCoord_symm, setIntegral_congr_fun
      polarCoord.open_target.measurableSet heq, volume_restrict_polarCoord_target,
      integral_prod_mul (fun r : ℝ => r * (1 + r ^ 2) ^ (-a)) (fun _ : ℝ => (1 : ℝ)),
      integral_Ioi_mul_one_add_sq_rpow_neg ha]
    have : a - 1 ≠ 0 := by linarith
    simp
    field_simp
    rw [max_eq_left (by positivity)]
    ring

/-- **Doubled circle mean value.** If `G` is holomorphic on the unit disc and `0 ≤ ρ < 1`, then
`∫_{(-π,π)} G (-ρ e^{-2iθ}) dθ = 2π G 0`. -/
theorem integral_Ioo_doubling_circle {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {G : ℂ → E} (hG : DifferentiableOn ℂ G (Metric.ball 0 1)) {ρ : ℝ}
    (h0 : 0 ≤ ρ) (h1 : ρ < 1) :
    ∫ θ in Ioo (-π) π, G (-(ρ : ℂ) * ((Real.cos θ : ℂ) - Real.sin θ * I) ^ 2) =
      (2 * π) • G 0 := by
  set R := √ρ with hR
  have hR1 : R < 1 := by
    rw [hR, Real.sqrt_lt' one_pos]; simpa using h1
  have hRsq : ((R : ℝ) : ℂ) ^ 2 = ρ := by
    rw [← ofReal_pow, hR, Real.sq_sqrt h0]
  set H : ℂ → E := fun z => G (-z ^ 2) with hH
  have hHd : DifferentiableOn ℂ H (Metric.ball 0 1) := by
    refine hG.comp (by fun_prop : Differentiable ℂ fun z : ℂ => -z ^ 2).differentiableOn ?_
    intro z hz
    simp only [Metric.mem_ball, dist_zero_right, norm_neg, norm_pow] at hz ⊢
    have := norm_nonneg z
    nlinarith
  have hcl : DiffContOnCl ℂ H (Metric.ball 0 |R|) := by
    refine DifferentiableOn.diffContOnCl (hHd.mono ?_)
    refine Metric.closure_ball_subset_closedBall.trans (Metric.closedBall_subset_ball ?_)
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]; exact hR1
  have hpt : ∀ θ : ℝ, G (-(ρ : ℂ) * ((Real.cos θ : ℂ) - Real.sin θ * I) ^ 2) =
      H (circleMap 0 R (-θ)) := by
    intro θ
    simp only [hH, circleMap, zero_add, mul_pow, hRsq]
    rw [exp_mul_I, ← ofReal_cos, ← ofReal_sin, Real.cos_neg, Real.sin_neg]
    push_cast
    ring_nf
  simp_rw [hpt]
  rw [← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
    intervalIntegral.integral_comp_neg (fun θ => H (circleMap 0 R θ)), neg_neg]
  have hper : Function.Periodic (fun θ => H (circleMap 0 R θ)) (2 * π) :=
    (periodic_circleMap 0 R).comp H
  have := hper.intervalIntegral_add_eq (-π) 0
  rw [show -π + 2 * π = π by ring, zero_add] at this
  rw [this]
  have hav := hcl.circleAverage
  rw [Real.circleAverage] at hav
  have hH0 : H 0 = G 0 := by simp [hH]
  rw [← hH0, ← hav, smul_inv_smul₀ (by positivity)]

/-- For `(s, t) ≠ 0`, the doubling factor `(s - t i)² / (s² + t²)` has modulus one. -/
theorem norm_doubling_factor {s t : ℝ} (h : (s, t) ≠ (0 : ℝ × ℝ)) :
    ‖((s : ℂ) - t * I) ^ 2 / ((s : ℂ) ^ 2 + (t : ℂ) ^ 2)‖ = 1 := by
  have hst : s ≠ 0 ∨ t ≠ 0 := by
    by_contra hc
    simp only [not_or, not_not] at hc
    exact h (by simp [hc.1, hc.2])
  have hpos : 0 < s ^ 2 + t ^ 2 := by
    rcases hst with hs | ht
    · have := sq_pos_of_ne_zero hs; nlinarith [sq_nonneg t]
    · have := sq_pos_of_ne_zero ht; nlinarith [sq_nonneg s]
  have hz : ‖(s : ℂ) - t * I‖ ^ 2 = s ^ 2 + t ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
  have hden : (s : ℂ) ^ 2 + (t : ℂ) ^ 2 = ((s ^ 2 + t ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [norm_div, norm_pow, hz, hden, Complex.norm_real, Real.norm_of_nonneg hpos.le,
    div_self hpos.ne']

/-- In polar coordinates `(s, t) = (r cos θ, r sin θ)` with `r > 0`, the doubling factor
`(s - t i)² / (s² + t²)` equals `(cos θ - i sin θ)²`. -/
theorem doubling_factor_polar {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    (((r * Real.cos θ : ℝ) : ℂ) - ((r * Real.sin θ : ℝ) : ℂ) * I) ^ 2 /
      (((r * Real.cos θ : ℝ) : ℂ) ^ 2 + ((r * Real.sin θ : ℝ) : ℂ) ^ 2) =
      ((Real.cos θ : ℂ) - Real.sin θ * I) ^ 2 := by
  have hcs : (Real.cos θ : ℂ) ^ 2 + (Real.sin θ : ℂ) ^ 2 = 1 := by
    rw [← ofReal_pow, ← ofReal_pow, ← ofReal_add, Real.cos_sq_add_sin_sq, ofReal_one]
  have hr0 : (r : ℂ) ≠ 0 := ofReal_ne_zero.2 hr.ne'
  have hden : ((r * Real.cos θ : ℝ) : ℂ) ^ 2 + ((r * Real.sin θ : ℝ) : ℂ) ^ 2 = (r : ℂ) ^ 2 := by
    simp only [ofReal_mul]; linear_combination (r : ℂ) ^ 2 * hcs
  rw [hden, div_eq_iff (pow_ne_zero 2 hr0)]
  simp only [ofReal_mul]; ring

/-- **Mean value under the angle-doubling disc map.** Let `F` be holomorphic on the unit disc with
values in a complex Banach space, let `ψ` be continuous with `0 ≤ ψ r < 1` for `r ≥ 0`, and put
`w (s, t) = -ψ (√(s² + t²)) · (s - t i)² / (s² + t²)`. If the radial weight `φ (√(s² + t²))` and
`φ (√(s² + t²)) ‖F (w (s, t))‖` are integrable on `ℝ × ℝ`, then
`∫ φ (√(s² + t²)) • F (w (s, t)) = (∫ φ (√(s² + t²))) • F 0`. -/
theorem integral_radial_smul_doubling_holomorphic {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] {F : ℂ → E} (hF : DifferentiableOn ℂ F (Metric.ball 0 1))
    {ψ : ℝ → ℝ} (hψc : Continuous ψ) (hψ0 : ∀ r, 0 ≤ r → 0 ≤ ψ r) (hψ1 : ∀ r, 0 ≤ r → ψ r < 1)
    (φ : ℝ → ℝ)
    (hint : Integrable (fun u : ℝ × ℝ => φ √(u.1 ^ 2 + u.2 ^ 2) *
      ‖F (-(ψ √(u.1 ^ 2 + u.2 ^ 2) : ℂ) *
        (((u.1 : ℂ) - u.2 * I) ^ 2 / ((u.1 : ℂ) ^ 2 + (u.2 : ℂ) ^ 2)))‖))
    (hφ : Integrable (fun u : ℝ × ℝ => φ √(u.1 ^ 2 + u.2 ^ 2))) :
    ∫ u : ℝ × ℝ, φ √(u.1 ^ 2 + u.2 ^ 2) •
        F (-(ψ √(u.1 ^ 2 + u.2 ^ 2) : ℂ) *
          (((u.1 : ℂ) - u.2 * I) ^ 2 / ((u.1 : ℂ) ^ 2 + (u.2 : ℂ) ^ 2))) =
      (∫ u : ℝ × ℝ, φ √(u.1 ^ 2 + u.2 ^ 2)) • F 0 := by
  set w : ℝ × ℝ → ℂ := fun u => -(ψ √(u.1 ^ 2 + u.2 ^ 2) : ℂ) *
    (((u.1 : ℂ) - u.2 * I) ^ 2 / ((u.1 : ℂ) ^ 2 + (u.2 : ℂ) ^ 2)) with hw
  have hden : ∀ u : ℝ × ℝ, u ≠ 0 → (u.1 : ℂ) ^ 2 + (u.2 : ℂ) ^ 2 ≠ 0 := by
    intro u hu h0
    have h1 := norm_doubling_factor (s := u.1) (t := u.2) (by simpa using hu)
    rw [h0, div_zero, norm_zero] at h1
    exact zero_ne_one h1
  have hwc : ContinuousOn w {0}ᶜ := by
    refine ContinuousOn.mul (by fun_prop) (ContinuousOn.div (by fun_prop) (by fun_prop) ?_)
    exact fun u hu => hden u hu
  have hmaps : MapsTo w {0}ᶜ (Metric.ball 0 1) := by
    intro u hu
    have hu' : (u.1, u.2) ≠ (0 : ℝ × ℝ) := by simpa using hu
    simp only [Metric.mem_ball, dist_zero_right, hw, norm_mul, norm_neg, norm_real,
      norm_doubling_factor hu', mul_one, Real.norm_eq_abs]
    rw [abs_of_nonneg (hψ0 _ (Real.sqrt_nonneg _))]
    exact hψ1 _ (Real.sqrt_nonneg _)
  have hFw : AEStronglyMeasurable (fun u => F (w u)) volume := by
    have := (hF.continuousOn.comp hwc hmaps).aestronglyMeasurable (μ := volume)
      (measurableSet_singleton (0 : ℝ × ℝ)).compl
    rwa [restrict_compl_singleton] at this
  have hint' : Integrable (fun u : ℝ × ℝ => φ √(u.1 ^ 2 + u.2 ^ 2) • F (w u)) :=
    Integrable.mono' hint.norm (hφ.aestronglyMeasurable.smul hFw)
      (ae_of_all _ fun u => by rw [norm_smul, norm_mul, norm_norm])
  rw [integral_eq_iterated_polar _ hint', integral_eq_iterated_polar _ hφ,
    ← integral_smul_const]
  refine setIntegral_congr_fun measurableSet_Ioi (fun r hr => ?_)
  have hr' : (0 : ℝ) < r := hr
  have hρ : ∀ θ : ℝ, √((polarCoord.symm (r, θ)).1 ^ 2 + (polarCoord.symm (r, θ)).2 ^ 2) = r := by
    intro θ
    rw [polarCoord_symm_sq_add_sq, Real.sqrt_sq hr'.le]
  have hwp : ∀ θ : ℝ, w (polarCoord.symm (r, θ)) =
      -(ψ r : ℂ) * ((Real.cos θ : ℂ) - Real.sin θ * I) ^ 2 := by
    intro θ
    simp only [hw, hρ]
    rw [polarCoord_symm_apply, doubling_factor_polar hr']
  simp only [hρ, hwp, smul_smul]
  rw [integral_smul, integral_Ioo_doubling_circle hF (hψ0 r hr'.le) (hψ1 r hr'.le),
    setIntegral_const, Real.volume_real_Ioo_of_le (by linarith [Real.pi_pos]), smul_smul,
    smul_eq_mul, smul_eq_mul]
  congr 1
  ring

/-- **Scalar mean value under the angle-doubling disc map.** The complex-valued case of
`integral_radial_smul_doubling_holomorphic`:
`∫ φ (√(s² + t²)) · F (w (s, t)) = F 0 · ∫ φ (√(s² + t²))`. -/
theorem integral_radial_mul_doubling_holomorphic {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F (Metric.ball 0 1))
    {ψ : ℝ → ℝ} (hψc : Continuous ψ) (hψ0 : ∀ r, 0 ≤ r → 0 ≤ ψ r) (hψ1 : ∀ r, 0 ≤ r → ψ r < 1)
    (φ : ℝ → ℝ)
    (hint : Integrable (fun u : ℝ × ℝ => φ √(u.1 ^ 2 + u.2 ^ 2) *
      ‖F (-(ψ √(u.1 ^ 2 + u.2 ^ 2) : ℂ) *
        (((u.1 : ℂ) - u.2 * I) ^ 2 / ((u.1 : ℂ) ^ 2 + (u.2 : ℂ) ^ 2)))‖))
    (hφ : Integrable (fun u : ℝ × ℝ => φ √(u.1 ^ 2 + u.2 ^ 2))) :
    ∫ u : ℝ × ℝ, (φ √(u.1 ^ 2 + u.2 ^ 2) : ℂ) *
        F (-(ψ √(u.1 ^ 2 + u.2 ^ 2) : ℂ) *
          (((u.1 : ℂ) - u.2 * I) ^ 2 / ((u.1 : ℂ) ^ 2 + (u.2 : ℂ) ^ 2))) =
      F 0 * ∫ u : ℝ × ℝ, (φ √(u.1 ^ 2 + u.2 ^ 2) : ℂ) := by
  have h := integral_radial_smul_doubling_holomorphic hF hψc hψ0 hψ1 φ hint hφ
  simp only [Complex.real_smul] at h
  rw [h, integral_complex_ofReal, mul_comm]

end TernaryPeriodPolynomials.AnalyticClasses
