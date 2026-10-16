module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.MeanValuePolar

@[expose] public section


/-!
# The angular integral of the real entry for a general holomorphic `h`

Mean value property in the form `∫_{-π}^{π} Ψ(e^{2iθ}) dθ = 2πΨ(0)`: for `h` holomorphic on the upper
half-plane the angular integral of `r⁻³ h(τ) bⁿ` over the polar circle of radius `ρ` equals the
angular integral for `h₀ = (τ+i)^{-(n+3)}` times `F(0) = (2i)^{n+3} h(i)`
(`inner_integral_scaling`).

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry

open TernaryPeriodPolynomials.Argument MeasureTheory Set

theorem entryAngularPoly_differentiable (n : ℕ) (r : ℝ) :
    Differentiable ℂ (entryAngularPoly n r) := by
  unfold entryAngularPoly entryQ
  fun_prop

/-- The angular integral of the real entry for a general holomorphic `h`: only the constant mode
of `Q_r³ Q_{1/r}ⁿ` survives, giving `F(0) = (2i)^{n+3} h(i)` times the polynomial's constant term. -/
theorem inner_integral_closed_form (h : ℂ → ℂ) (hh : DifferentiableOn ℂ h {z : ℂ | 0 < z.im})
    (n : ℕ) (ρ : ℝ) (hρ : 0 < ρ) :
    ∫ θ in Set.Ioo (-Real.pi) Real.pi, ρ • entryIntegrandOf h n (ρ * Real.sin θ, ρ * Real.cos θ) =
      (ρ : ℂ) * entryPolarScalar n (Real.sqrt (1 + ρ ^ 2)) *
        (2 * Real.pi * (entryAngularPoly n (Real.sqrt (1 + ρ ^ 2)) 0 * entryDiscFn n h 0)) := by
  set r := Real.sqrt (1 + ρ ^ 2) with hr_def
  have hr2 : r ^ 2 = 1 + ρ ^ 2 := Real.sq_sqrt (by positivity)
  have hr : 0 < r := Real.sqrt_pos.mpr (by positivity)
  have hr1 : 1 ≤ r := by nlinarith [sq_nonneg ρ]
  set Ψ : ℂ → ℂ := fun ζ => entryAngularPoly n r ζ *
    entryDiscFn n h ((cayleyRadius r : ℂ) * ζ) with hΨdef
  have hdiff : DifferentiableOn ℂ Ψ (Metric.closedBall 0 1) := by
    refine ((entryAngularPoly_differentiable n r).differentiableOn).mul ?_
    have hmaps : Set.MapsTo (fun ζ : ℂ => (cayleyRadius r : ℂ) * ζ) (Metric.closedBall 0 1)
        (Metric.ball 0 1) := by
      intro ζ hζ
      rw [mem_ball_zero_iff, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (cayleyRadius_nonneg hr1)]
      rw [mem_closedBall_zero_iff] at hζ
      calc cayleyRadius r * ‖ζ‖ ≤ cayleyRadius r * 1 :=
            mul_le_mul_of_nonneg_left hζ (cayleyRadius_nonneg hr1)
        _ < 1 := by rw [mul_one]; exact cayleyRadius_lt_one hr
    exact (entryDiscFn_differentiableOn n h hh).comp
      ((differentiableOn_const _).mul differentiableOn_id) hmaps
  have hΨ : DiffContOnCl ℂ Ψ (Metric.ball 0 1) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball (0 : ℂ) one_ne_zero]
    exact hdiff
  have pt : ∀ θ : ℝ, ρ • entryIntegrandOf h n (ρ * Real.sin θ, ρ * Real.cos θ) =
      ((ρ : ℂ) * entryPolarScalar n r) * Ψ (Complex.exp (2 * Complex.I * θ)) := by
    intro θ
    rw [Complex.real_smul, entryIntegrandOf_polar h n ρ θ r hr2 hr]
    simp only [hΨdef]
    ring
  simp_rw [pt]
  rw [MeasureTheory.integral_const_mul, integral_comp_exp_two_mul Ψ hΨ]
  simp only [hΨdef, mul_zero]


/-- The `h₀ = (τ + i)^{-(n+3)}` is holomorphic on the upper half-plane. -/
theorem entryH0_differentiableOn (n : ℕ) :
    DifferentiableOn ℂ (fun τ : ℂ => (τ + Complex.I) ^ (-((n : ℤ) + 3))) {z : ℂ | 0 < z.im} := by
  intro z hz
  have hne : z + Complex.I ≠ 0 := by
    intro h0
    have := congrArg Complex.im h0
    simp at this
    have hz' : 0 < z.im := hz
    linarith
  have hd : DifferentiableAt ℂ (fun τ : ℂ => τ + Complex.I) z := differentiableAt_id.add_const _
  exact (hd.zpow (Or.inl hne)).differentiableWithinAt

theorem entryDiscFn_zero (n : ℕ) (h : ℂ → ℂ) :
    entryDiscFn n h 0 = (2 * Complex.I) ^ (n + 3) * h Complex.I := by
  simp [entryDiscFn]

theorem entryDiscFn_zero_h0 (n : ℕ) :
    entryDiscFn n (fun τ : ℂ => (τ + Complex.I) ^ (-((n : ℤ) + 3))) 0 = 1 := by
  rw [entryDiscFn_zero]
  have hne : (Complex.I + Complex.I) ≠ 0 := by
    rw [← two_mul]; exact mul_ne_zero two_ne_zero Complex.I_ne_zero
  rw [show (-((n : ℤ) + 3)) = -((n + 3 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast,
    ← two_mul]
  exact mul_inv_cancel₀ (pow_ne_zero _ (by rw [two_mul]; exact hne))

/-- **The angular integral scales with `F(0) = (2i)^{n+3} h(i)`.** -/
theorem inner_integral_scaling (h : ℂ → ℂ) (hh : DifferentiableOn ℂ h {z : ℂ | 0 < z.im})
    (n : ℕ) (ρ : ℝ) (hρ : 0 < ρ) :
    ∫ θ in Set.Ioo (-Real.pi) Real.pi, ρ • entryIntegrandOf h n (ρ * Real.sin θ, ρ * Real.cos θ) =
      (∫ θ in Set.Ioo (-Real.pi) Real.pi, ρ • entryIntegrand n (ρ * Real.sin θ, ρ * Real.cos θ)) *
        ((2 * Complex.I) ^ (n + 3) * h Complex.I) := by
  rw [inner_integral_closed_form h hh n ρ hρ, entryIntegrand_eq_entryIntegrandOf,
    inner_integral_closed_form _ (entryH0_differentiableOn n) n ρ hρ, entryDiscFn_zero_h0,
    entryDiscFn_zero]
  ring

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
