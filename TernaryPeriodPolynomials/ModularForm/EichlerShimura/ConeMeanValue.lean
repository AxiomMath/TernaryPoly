module

public import Mathlib

@[expose] public section


/-!
# A sub-mean-value inequality for holomorphic functions on a disc

Foundation file of the unconditional Eichler--Shimura route.  If `h` is holomorphic on the closed disc `D̄(z₀, r)` then
`(π r² / 3) |h(z₀)|² ≤ ∫ max(0, 1 - |z - z₀| / r) · |h(z)|² dA` (`cone_mean_value`).  Proof: the
circle mean value property and Cauchy--Schwarz give
`2π |h(z₀)|² ≤ ∫_{-π}^{π} |h(z₀ + s e^{iθ})|² dθ` for `0 < s ≤ r` (`circle_sq_le`,
`angular_lintegral_ge`), integrated against `s (1 - s/r) ds` in polar coordinates.

Formalized by Claude Sonnet 5.5.
-/

open Complex MeasureTheory Set Metric intervalIntegral
open scoped Real

noncomputable section

open scoped Classical

namespace TernaryPeriodPolynomials.Argument.ESFoundations.ConeMeanValue

theorem circle_sq_le {h : ℂ → ℂ} {z0 : ℂ} {r s : ℝ} (hs : 0 < s) (hsr : s ≤ r)
    (hh : DifferentiableOn ℂ h (closedBall z0 r)) :
    2 * π * ‖h z0‖ ^ 2 ≤ ∫ θ in (0 : ℝ)..(2 * π), ‖h (circleMap z0 s θ)‖ ^ 2 := by
  have hcm : ∀ θ, circleMap z0 s θ ∈ closedBall z0 r := fun θ => by
    have := circleMap_mem_sphere z0 hs.le θ
    exact closedBall_subset_closedBall hsr (sphere_subset_closedBall this)
  have hcont : Continuous fun θ => h (circleMap z0 s θ) :=
    hh.continuousOn.comp_continuous (continuous_circleMap z0 s) hcm
  have hdc : DiffContOnCl ℂ h (ball z0 |s|) := by
    refine ⟨?_, ?_⟩
    · exact hh.mono (ball_subset_closedBall.trans (closedBall_subset_closedBall
        (by rw [abs_of_pos hs]; exact hsr)))
    · rw [abs_of_pos hs, closure_ball z0 hs.ne']
      exact hh.continuousOn.mono (closedBall_subset_closedBall hsr)
  have h1 : Real.circleAverage h z0 s = h z0 := hdc.circleAverage
  rw [Real.circleAverage_def] at h1
  set a : ℝ := ∫ θ in (0 : ℝ)..(2 * π), ‖h (circleMap z0 s θ)‖ with ha
  set b : ℝ := ∫ θ in (0 : ℝ)..(2 * π), ‖h (circleMap z0 s θ)‖ ^ 2 with hb
  have hpi : 0 < π := Real.pi_pos
  have hint1 : IntervalIntegrable (fun θ => ‖h (circleMap z0 s θ)‖) volume 0 (2 * π) :=
    (hcont.norm).intervalIntegrable _ _
  have hint2 : IntervalIntegrable (fun θ => ‖h (circleMap z0 s θ)‖ ^ 2) volume 0 (2 * π) :=
    ((hcont.norm).pow 2).intervalIntegrable _ _
  -- ‖h z0‖ ≤ a / (2π)
  have hn : ‖h z0‖ ≤ (2 * π)⁻¹ * a := by
    rw [← h1, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 (by positivity))]
    exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm (by positivity))
      (inv_nonneg.2 (by positivity))
  -- a² ≤ 2π b
  have hab : a ^ 2 ≤ 2 * π * b := by
    have hc : 0 ≤ ∫ θ in (0 : ℝ)..(2 * π), (‖h (circleMap z0 s θ)‖ - a / (2 * π)) ^ 2 :=
      intervalIntegral.integral_nonneg (by positivity) (fun θ _ => sq_nonneg _)
    have : ∫ θ in (0 : ℝ)..(2 * π), (‖h (circleMap z0 s θ)‖ - a / (2 * π)) ^ 2 =
        b - a ^ 2 / (2 * π) := by
      have e : ∀ θ, (‖h (circleMap z0 s θ)‖ - a / (2 * π)) ^ 2 =
          ‖h (circleMap z0 s θ)‖ ^ 2 - 2 * (a / (2 * π)) * ‖h (circleMap z0 s θ)‖ +
            (a / (2 * π)) ^ 2 := fun θ => by ring
      simp_rw [e]
      rw [intervalIntegral.integral_add (hint2.sub (hint1.const_mul _)) intervalIntegrable_const,
        intervalIntegral.integral_sub hint2 (hint1.const_mul _),
        intervalIntegral.integral_const_mul]
      simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
      field_simp
      ring
    rw [this] at hc
    have : a ^ 2 / (2 * π) ≤ b := by linarith
    rw [div_le_iff₀ (by positivity)] at this
    linarith
  have ha0 : 0 ≤ a := intervalIntegral.integral_nonneg (by positivity) (fun θ _ => norm_nonneg _)
  calc 2 * π * ‖h z0‖ ^ 2 ≤ 2 * π * ((2 * π)⁻¹ * a) ^ 2 := by
        gcongr
    _ = a ^ 2 / (2 * π) := by field_simp
    _ ≤ b := by
        rw [div_le_iff₀ (by positivity)]
        linarith

theorem circleMap_eq_polar (z0 : ℂ) (s θ : ℝ) :
    circleMap z0 s θ = z0 + (s : ℂ) * (Real.cos θ + Real.sin θ * Complex.I) := by
  rw [circleMap, Complex.exp_mul_I]
  simp [Complex.ofReal_cos, Complex.ofReal_sin]

/-- The inner (angular) integral in polar coordinates dominates `2π |h(z₀)|²`. -/
theorem angular_lintegral_ge {h : ℂ → ℂ} {z0 : ℂ} {r s : ℝ} (hs : 0 < s) (hsr : s ≤ r)
    (hh : DifferentiableOn ℂ h (closedBall z0 r)) :
    ENNReal.ofReal (2 * π * ‖h z0‖ ^ 2) ≤
      ∫⁻ θ in Ioo (-π) π, ENNReal.ofReal
        (‖h (z0 + (s : ℂ) * (Real.cos θ + Real.sin θ * Complex.I))‖ ^ 2) := by
  have h1 := circle_sq_le hs hsr hh
  have hcm : ∀ θ, circleMap z0 s θ ∈ closedBall z0 r := fun θ => by
    have := circleMap_mem_sphere z0 hs.le θ
    exact closedBall_subset_closedBall hsr (sphere_subset_closedBall this)
  have hcont : Continuous fun θ => ‖h (circleMap z0 s θ)‖ ^ 2 :=
    ((hh.continuousOn.comp_continuous (continuous_circleMap z0 s) hcm).norm).pow 2
  have hper : Function.Periodic (fun θ : ℝ => ‖h (circleMap z0 s θ)‖ ^ 2) (2 * π) := fun θ => by
    simp [circleMap, add_mul, Complex.exp_add, Complex.exp_two_pi_mul_I]
  have h2 : ∫ θ in (0 : ℝ)..(2 * π), ‖h (circleMap z0 s θ)‖ ^ 2 =
      ∫ θ in (-π)..π, ‖h (circleMap z0 s θ)‖ ^ 2 := by
    have := hper.intervalIntegral_add_eq (-π) 0
    rw [show (-π) + 2 * π = π by ring] at this
    rw [zero_add] at this
    exact this.symm
  have h3 : ∫ θ in (-π)..π, ‖h (circleMap z0 s θ)‖ ^ 2 =
      ∫ θ in Ioo (-π) π, ‖h (circleMap z0 s θ)‖ ^ 2 := by
    rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos]), integral_Ioc_eq_integral_Ioo]
  rw [h2, h3] at h1
  have hint : IntegrableOn (fun θ => ‖h (circleMap z0 s θ)‖ ^ 2) (Ioo (-π) π) :=
    hcont.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have h5 := ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun θ => sq_nonneg _)
  calc ENNReal.ofReal (2 * π * ‖h z0‖ ^ 2) ≤
        ENNReal.ofReal (∫ θ in Ioo (-π) π, ‖h (circleMap z0 s θ)‖ ^ 2) :=
        ENNReal.ofReal_le_ofReal h1
    _ = _ := by
        rw [h5]
        simp only [circleMap_eq_polar]

/-- `∫_0^r s (1 - s/r) ds = r²/6` as a `lintegral`. -/
theorem lintegral_cone_weight {r : ℝ} (hr : 0 < r) :
    ∫⁻ s in Ioc (0 : ℝ) r, ENNReal.ofReal (s * (1 - s / r)) = ENNReal.ofReal (r ^ 2 / 6) := by
  have hint : IntegrableOn (fun s : ℝ => s * (1 - s / r)) (Ioc 0 r) :=
    (by fun_prop : Continuous fun s : ℝ => s * (1 - s / r)).integrableOn_Icc.mono_set
      Ioc_subset_Icc_self
  have hnn : ∀ s ∈ Ioc (0 : ℝ) r, 0 ≤ s * (1 - s / r) := fun s hs => by
    have : s / r ≤ 1 := (div_le_one hr).2 hs.2
    exact mul_nonneg hs.1.le (by linarith)
  rw [← ofReal_integral_eq_lintegral_ofReal hint ((ae_restrict_iff' measurableSet_Ioc).2
    (Filter.Eventually.of_forall hnn))]
  congr 1
  rw [← intervalIntegral.integral_of_le hr.le]
  have : ∀ s : ℝ, s * (1 - s / r) = s - s ^ 2 / r := fun s => by ring
  simp_rw [this]
  rw [intervalIntegral.integral_sub intervalIntegral.intervalIntegrable_id
    ((continuous_pow 2).div_const r |>.intervalIntegrable _ _), integral_id,
    intervalIntegral.integral_div, integral_pow]
  field_simp
  ring

/-- The cone-weighted density, with `h` cut off to the closed disc. -/
def coneG (h : ℂ → ℂ) (z0 : ℂ) (r : ℝ) (z : ℂ) : ℝ :=
  max 0 (1 - ‖z - z0‖ / r) * ‖(closedBall z0 r).indicator h z‖ ^ 2

theorem measurable_coneG {h : ℂ → ℂ} {z0 : ℂ} {r : ℝ}
    (hh : DifferentiableOn ℂ h (closedBall z0 r)) : Measurable (coneG h z0 r) := by
  have hm : Measurable ((closedBall z0 r).indicator h) := by
    have := hh.continuousOn.measurable_piecewise (g := fun _ => (0 : ℂ)) continuousOn_const
      measurableSet_closedBall
    convert this using 1
    funext z
    simp [Set.indicator, Set.piecewise]
  unfold coneG
  refine Measurable.mul ?_ (hm.norm.pow_const 2)
  refine Measurable.max measurable_const ?_
  exact measurable_const.sub ((measurable_id.sub measurable_const).norm.div_const r)

theorem cone_lintegral_ge {h : ℂ → ℂ} {z0 : ℂ} {r : ℝ} (hr : 0 < r)
    (hh : DifferentiableOn ℂ h (closedBall z0 r)) :
    ENNReal.ofReal (π * r ^ 2 / 3 * ‖h z0‖ ^ 2) ≤ ∫⁻ z, ENNReal.ofReal (coneG h z0 r z) := by
  have hmeas : Measurable fun z => ENNReal.ofReal (coneG h z0 r z) :=
    ENNReal.measurable_ofReal.comp (measurable_coneG hh)
  have h1 : ∫⁻ z, ENNReal.ofReal (coneG h z0 r z) =
      ∫⁻ w, ENNReal.ofReal (coneG h z0 r (z0 + w)) := by
    rw [lintegral_add_left_eq_self (fun z => ENNReal.ofReal (coneG h z0 r z)) z0]
  rw [h1, ← Complex.lintegral_comp_polarCoord_symm]
  rw [polarCoord_target]
  simp only [Complex.polarCoord_symm_apply, smul_eq_mul]
  rw [Measure.volume_eq_prod, setLIntegral_prod _ (by
    refine Measurable.aemeasurable ?_
    have : Measurable fun p : ℝ × ℝ => z0 + (p.1 : ℂ) *
        ((Real.cos p.2 : ℂ) + (Real.sin p.2 : ℂ) * Complex.I) := by fun_prop
    exact (ENNReal.measurable_ofReal.comp measurable_fst).mul
      (hmeas.comp this))]
  have hsub : Ioc (0 : ℝ) r ⊆ Ioi 0 := fun x hx => hx.1
  refine le_trans ?_ (lintegral_mono_set hsub)
  have hpt : ∀ x ∈ Ioc (0 : ℝ) r,
      ENNReal.ofReal (x * (1 - x / r)) * ENNReal.ofReal (2 * π * ‖h z0‖ ^ 2) ≤
      ∫⁻ y in Ioo (-π) π, ENNReal.ofReal (x, y).1 *
        ENNReal.ofReal (coneG h z0 r (z0 + ↑(x, y).1 *
          (↑(Real.cos (x, y).2) + ↑(Real.sin (x, y).2) * Complex.I))) := by
    intro x hx
    have hx0 : 0 < x := hx.1
    have hxr : x ≤ r := hx.2
    have hcone : ∀ y : ℝ, coneG h z0 r (z0 + (x : ℂ) * (Real.cos y + Real.sin y * Complex.I)) =
        (1 - x / r) * ‖h (z0 + (x : ℂ) * (Real.cos y + Real.sin y * Complex.I))‖ ^ 2 := by
      intro y
      have hn : ‖(x : ℂ) * (Real.cos y + Real.sin y * Complex.I)‖ = x := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]
        have : ‖(Real.cos y : ℂ) + (Real.sin y : ℂ) * Complex.I‖ = 1 := by
          rw [Complex.ofReal_cos, Complex.ofReal_sin, ← Complex.exp_mul_I]
          simp
        rw [this, mul_one]
      have hmem : z0 + (x : ℂ) * (Real.cos y + Real.sin y * Complex.I) ∈ closedBall z0 r := by
        rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, hn]; exact hxr
      unfold coneG
      rw [Set.indicator_of_mem hmem, add_sub_cancel_left, hn, max_eq_right]
      have : x / r ≤ 1 := (div_le_one hr).2 hxr
      linarith
    simp only [hcone]
    have hnn : 0 ≤ 1 - x / r := by
      have : x / r ≤ 1 := (div_le_one hr).2 hxr
      linarith
    have e : ∀ y : ℝ, ENNReal.ofReal x * ENNReal.ofReal ((1 - x / r) *
        ‖h (z0 + (x : ℂ) * (Real.cos y + Real.sin y * Complex.I))‖ ^ 2) =
        ENNReal.ofReal (x * (1 - x / r)) * ENNReal.ofReal
          (‖h (z0 + (x : ℂ) * (Real.cos y + Real.sin y * Complex.I))‖ ^ 2) := by
      intro y
      rw [← ENNReal.ofReal_mul hx0.le, ← ENNReal.ofReal_mul (mul_nonneg hx0.le hnn)]
      congr 1; ring
    simp only [e]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact mul_le_mul' le_rfl (angular_lintegral_ge hx0 hxr hh)
  calc ENNReal.ofReal (π * r ^ 2 / 3 * ‖h z0‖ ^ 2)
      = (∫⁻ x in Ioc (0 : ℝ) r, ENNReal.ofReal (x * (1 - x / r))) *
          ENNReal.ofReal (2 * π * ‖h z0‖ ^ 2) := by
        rw [lintegral_cone_weight hr, ← ENNReal.ofReal_mul (by positivity)]
        congr 1; ring
    _ = ∫⁻ x in Ioc (0 : ℝ) r, ENNReal.ofReal (x * (1 - x / r)) *
          ENNReal.ofReal (2 * π * ‖h z0‖ ^ 2) := by
        rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
    _ ≤ _ := setLIntegral_mono' measurableSet_Ioc hpt

theorem coneG_nonneg (h : ℂ → ℂ) (z0 : ℂ) (r : ℝ) (z : ℂ) : 0 ≤ coneG h z0 r z := by
  unfold coneG
  exact mul_nonneg (le_max_left _ _) (sq_nonneg _)

theorem integrable_coneG {h : ℂ → ℂ} {z0 : ℂ} {r : ℝ} (hr : 0 < r)
    (hh : DifferentiableOn ℂ h (closedBall z0 r)) : Integrable (coneG h z0 r) := by
  obtain ⟨M, hM⟩ := (isCompact_closedBall z0 r).exists_bound_of_continuousOn hh.continuousOn
  refine Integrable.mono' ((integrable_indicator_iff measurableSet_closedBall).2
    (integrableOn_const (C := M ^ 2) (isCompact_closedBall z0 r).measure_lt_top.ne)) 
    (measurable_coneG hh).aestronglyMeasurable (Filter.Eventually.of_forall fun z => ?_)
  by_cases hz : z ∈ closedBall z0 r
  · rw [Real.norm_eq_abs, abs_of_nonneg (coneG_nonneg h z0 r z), Set.indicator_of_mem hz]
    unfold coneG
    rw [Set.indicator_of_mem hz]
    have h1 : max 0 (1 - ‖z - z0‖ / r) ≤ 1 := by
      refine max_le zero_le_one ?_
      have : 0 ≤ ‖z - z0‖ / r := by positivity
      linarith
    have h2 : ‖h z‖ ^ 2 ≤ M ^ 2 := by
      have := hM z hz
      have h0 := norm_nonneg (h z)
      nlinarith
    calc max 0 (1 - ‖z - z0‖ / r) * ‖h z‖ ^ 2 ≤ 1 * M ^ 2 := by
          exact mul_le_mul h1 h2 (sq_nonneg _) zero_le_one
      _ = M ^ 2 := one_mul _
  · have : coneG h z0 r z = 0 := by
      unfold coneG
      rw [Set.indicator_of_notMem hz]; simp
    rw [this, Set.indicator_of_notMem hz]; simp

/-- **Sub-mean-value inequality with a cone weight**. -/
theorem cone_mean_value {h : ℂ → ℂ} {z0 : ℂ} {r : ℝ} (hr : 0 < r)
    (hh : DifferentiableOn ℂ h (closedBall z0 r)) :
    π * r ^ 2 / 3 * ‖h z0‖ ^ 2 ≤ ∫ z, coneG h z0 r z := by
  have h1 := cone_lintegral_ge hr hh
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_coneG hr hh)
    (Filter.Eventually.of_forall fun z => coneG_nonneg h z0 r z)] at h1
  exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg fun z => coneG_nonneg h z0 r z)).1 h1

end TernaryPeriodPolynomials.Argument.ESFoundations.ConeMeanValue
