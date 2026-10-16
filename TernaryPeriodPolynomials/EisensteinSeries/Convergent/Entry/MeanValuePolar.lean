module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.MeanValueAngular
public import TernaryPeriodPolynomials.BoundaryComparison.RealEntry.IntegrandPolar
public import TernaryPeriodPolynomials.BoundaryComparison.RealEntry.PeriodicityBridge

@[expose] public section


/-!
# Polar form of the real-entry integrand for a general function `h`

For `h : ℂ → ℂ` put `entryIntegrandOf h n (s,t) = r⁻³ h(τ) bⁿ` (the `entryIntegrand n` is
the case `h₀ = (τ+i)^{-(n+3)}`).  At the polar point `(ρ sin θ, ρ cos θ)`, with `r² = 1 + ρ²` and
`ζ = e^{2iθ}`, the Cayley variable `w = (τ - i)/(τ + i)` equals `((r-1)/(r+1)) ζ` and
`r⁻³ h(τ) bⁿ = scalar(r) · Q_r(ζ)³ Q_{1/r}(ζ)ⁿ · F(w)` with `F(w) = (2i/(1-w))^{n+3} h(i(1+w)/(1-w))`
(`entryIntegrandOf_polar`).  `F` is holomorphic on the unit disc if `h` is holomorphic on the upper
half-plane (`entryDiscFn_differentiableOn`).

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry

open TernaryPeriodPolynomials.Argument MeasureTheory Set

/-- The integrand `r⁻³ h(τ) bⁿ` of the real entry for a general function `h` on the upper
half-plane (the `entryIntegrand` is the case `h = (τ + i)^{-(n+3)}`). -/
def entryIntegrandOf (h : ℂ → ℂ) (n : ℕ) (st : ℝ × ℝ) : ℂ :=
  (entryRadius st : ℂ) ^ (-3 : ℤ) * h (entryTau st) * entryCoefficient st ^ n

/-- The `entryIntegrand n` is `entryIntegrandOf` of `h₀ = (τ + i)^{-(n+3)}`. -/
theorem entryIntegrand_eq_entryIntegrandOf (n : ℕ) :
    entryIntegrand n = entryIntegrandOf (fun τ => (τ + Complex.I) ^ (-((n : ℤ) + 3))) n := by
  funext st
  rfl

/-- `entryIntegrandOf h n = entryIntegrand n · ((τ + i)^{n+3} h(τ))`. -/
theorem entryIntegrandOf_eq (h : ℂ → ℂ) (n : ℕ) (st : ℝ × ℝ) :
    entryIntegrandOf h n st =
      entryIntegrand n st * ((entryTau st + Complex.I) ^ (n + 3) * h (entryTau st)) := by
  have hne : entryTau st + Complex.I ≠ 0 := entryTau_add_I_ne_zero st
  unfold entryIntegrandOf entryIntegrand
  have hz : (entryTau st + Complex.I) ^ (-((n : ℤ) + 3)) * (entryTau st + Complex.I) ^ (n + 3) = 1 := by
    rw [show (-((n : ℤ) + 3)) = -((n + 3 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast]
    exact inv_mul_cancel₀ (pow_ne_zero _ hne)
  linear_combination (-(↑(entryRadius st) : ℂ) ^ (-3 : ℤ) * entryCoefficient st ^ n * h (entryTau st)) * hz

/-- The ratio `(r - 1)/(r + 1)`, the radius of the circle on which `w = (τ - i)/(τ + i)` moves. -/
def cayleyRadius (r : ℝ) : ℝ := (r - 1) / (r + 1)

theorem cayleyRadius_nonneg {r : ℝ} (hr : 1 ≤ r) : 0 ≤ cayleyRadius r :=
  div_nonneg (by linarith) (by linarith)

theorem cayleyRadius_lt_one {r : ℝ} (hr : 0 < r) : cayleyRadius r < 1 := by
  unfold cayleyRadius
  rw [div_lt_one (by linarith)]
  linarith

/-- On the polar circle, `τ + i = 2i/(1 - w)` for `w = ((r-1)/(r+1)) e^{2iθ}`. -/
theorem entryTau_add_I_cayley (ρ θ r : ℝ) (hr2 : r ^ 2 = 1 + ρ ^ 2) (hr : 0 < r) :
    entryTau (ρ * Real.sin θ, ρ * Real.cos θ) + Complex.I =
      2 * Complex.I / (1 - (cayleyRadius r : ℂ) * Complex.exp (2 * Complex.I * θ)) := by
  rw [entryTau_add_I_polar ρ θ r hr2 hr, cos_sub_I_mul_sin_eq_exp_mul_entryQ r θ]
  have hQ : entryQ r (Complex.exp (2 * Complex.I * θ)) ≠ 0 := by
    intro h0
    have := c_sub_I_r_v_ne_zero r θ hr.ne'
    rw [cos_sub_I_mul_sin_eq_exp_mul_entryQ r θ, h0, mul_zero] at this
    exact this rfl
  have hr1 : (r : ℂ) + 1 ≠ 0 := by exact_mod_cast (by linarith : r + 1 ≠ 0)
  have hE : Complex.exp (-(Complex.I * θ)) ≠ 0 := Complex.exp_ne_zero _
  have h1 : 1 - (cayleyRadius r : ℂ) * Complex.exp (2 * Complex.I * θ) =
      2 * entryQ r (Complex.exp (2 * Complex.I * θ)) / ((r : ℂ) + 1) := by
    unfold cayleyRadius entryQ
    push_cast
    field_simp
    ring
  rw [h1]
  field_simp


theorem norm_cayley_mul (r θ : ℝ) (hr : 1 ≤ r) :
    ‖(cayleyRadius r : ℂ) * Complex.exp (2 * Complex.I * θ)‖ = cayleyRadius r := by
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (cayleyRadius_nonneg hr)]
  have : Complex.exp (2 * Complex.I * θ) = Complex.exp (((2 * θ : ℝ) : ℂ) * Complex.I) := by
    congr 1; push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I, mul_one]

theorem one_sub_cayley_ne_zero (ρ θ r : ℝ) (hr2 : r ^ 2 = 1 + ρ ^ 2) (hr : 0 < r) :
    1 - (cayleyRadius r : ℂ) * Complex.exp (2 * Complex.I * θ) ≠ 0 := by
  have hr1 : 1 ≤ r := by nlinarith [sq_nonneg ρ]
  intro h0
  have h1 : (cayleyRadius r : ℂ) * Complex.exp (2 * Complex.I * θ) = 1 := by linear_combination -h0
  have := congrArg norm h1
  rw [norm_cayley_mul r θ hr1, norm_one] at this
  linarith [cayleyRadius_lt_one hr]

/-- On the polar circle, `τ = i(1 + w)/(1 - w)` for `w = ((r-1)/(r+1)) e^{2iθ}`. -/
theorem entryTau_cayley (ρ θ r : ℝ) (hr2 : r ^ 2 = 1 + ρ ^ 2) (hr : 0 < r) :
    entryTau (ρ * Real.sin θ, ρ * Real.cos θ) =
      Complex.I * (1 + (cayleyRadius r : ℂ) * Complex.exp (2 * Complex.I * θ)) /
        (1 - (cayleyRadius r : ℂ) * Complex.exp (2 * Complex.I * θ)) := by
  have h := entryTau_add_I_cayley ρ θ r hr2 hr
  have hne := one_sub_cayley_ne_zero ρ θ r hr2 hr
  have : entryTau (ρ * Real.sin θ, ρ * Real.cos θ) =
      2 * Complex.I / (1 - (cayleyRadius r : ℂ) * Complex.exp (2 * Complex.I * θ)) - Complex.I := by
    rw [← h]; ring
  rw [this]
  field_simp
  ring

/-- The function `F(w) = (2i/(1-w))^{n+3} h(i(1+w)/(1-w)) = (τ+i)^{n+3} h(τ)` on the unit disc. -/
def entryDiscFn (n : ℕ) (h : ℂ → ℂ) (w : ℂ) : ℂ :=
  (2 * Complex.I / (1 - w)) ^ (n + 3) * h (Complex.I * (1 + w) / (1 - w))

/-- The scalar relating `entryIntegrand n` to `angularIntegrand n r` (see `entryIntegrand_polar`). -/
def entryPolarScalar (n : ℕ) (r : ℝ) : ℂ :=
  (-1 : ℂ) ^ n * (r : ℂ)⁻¹ ^ 3 / (Complex.I ^ (n + 3) * ((r : ℂ) + 1) ^ (n + 3))

/-- **Polar form of the general real-entry integrand:**
`r⁻³ h(τ) bⁿ = scalar(r) · Q_r(ζ)³ Q_{1/r}(ζ)ⁿ · F(((r-1)/(r+1)) ζ)` with `ζ = e^{2iθ}`. -/
theorem entryIntegrandOf_polar (h : ℂ → ℂ) (n : ℕ) (ρ θ r : ℝ) (hr2 : r ^ 2 = 1 + ρ ^ 2)
    (hr : 0 < r) :
    entryIntegrandOf h n (ρ * Real.sin θ, ρ * Real.cos θ) =
      entryPolarScalar n r * (entryAngularPoly n r (Complex.exp (2 * Complex.I * θ)) *
        entryDiscFn n h ((cayleyRadius r : ℂ) * Complex.exp (2 * Complex.I * θ))) := by
  rw [entryIntegrandOf_eq, entryIntegrand_polar n ρ θ r hr2 hr,
    angularIntegrand_eq_entryAngularPoly, entryTau_add_I_cayley ρ θ r hr2 hr,
    entryTau_cayley ρ θ r hr2 hr]
  unfold entryDiscFn entryPolarScalar
  ring

theorem cayley_im_pos (w : ℂ) (hw : ‖w‖ < 1) : 0 < (Complex.I * (1 + w) / (1 - w)).im := by
  have hne : (1 - w) ≠ 0 := by
    intro h0
    have : w = 1 := by linear_combination -h0
    rw [this, norm_one] at hw
    exact lt_irrefl _ hw
  have hns : 0 < Complex.normSq (1 - w) := Complex.normSq_pos.mpr hne
  have hw2 : w.re ^ 2 + w.im ^ 2 < 1 := by
    have := Complex.sq_norm w
    rw [Complex.normSq_apply] at this
    nlinarith [norm_nonneg w]
  rw [Complex.div_im]
  simp [Complex.normSq_apply] at hns ⊢
  exact (div_lt_div_iff_of_pos_right hns).mpr (by nlinarith)


/-- `F` is holomorphic on the unit disc when `h` is holomorphic on the upper half-plane. -/
theorem entryDiscFn_differentiableOn (n : ℕ) (h : ℂ → ℂ)
    (hh : DifferentiableOn ℂ h {z : ℂ | 0 < z.im}) :
    DifferentiableOn ℂ (entryDiscFn n h) (Metric.ball (0 : ℂ) 1) := by
  have hne : ∀ w ∈ Metric.ball (0 : ℂ) 1, (1 - w) ≠ 0 := by
    intro w hw h0
    have : w = 1 := by linear_combination -h0
    rw [mem_ball_zero_iff, this, norm_one] at hw
    exact lt_irrefl _ hw
  have hcay : DifferentiableOn ℂ (fun w : ℂ => Complex.I * (1 + w) / (1 - w))
      (Metric.ball (0 : ℂ) 1) := by
    intro w hw
    exact (((differentiableAt_const _).mul (differentiableAt_const _ |>.add differentiableAt_id)).div
      ((differentiableAt_const _).sub differentiableAt_id) (hne w hw)).differentiableWithinAt
  have hmaps : Set.MapsTo (fun w : ℂ => Complex.I * (1 + w) / (1 - w)) (Metric.ball (0 : ℂ) 1)
      {z : ℂ | 0 < z.im} := fun w hw => cayley_im_pos w (mem_ball_zero_iff.mp hw)
  have h1 : DifferentiableOn ℂ (fun w : ℂ => (2 * Complex.I / (1 - w)) ^ (n + 3))
      (Metric.ball (0 : ℂ) 1) := by
    intro w hw
    exact ((((differentiableAt_const _).div ((differentiableAt_const _).sub differentiableAt_id)
      (hne w hw)).pow (n + 3))).differentiableWithinAt
  exact h1.mul (hh.comp hcay hmaps)

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
