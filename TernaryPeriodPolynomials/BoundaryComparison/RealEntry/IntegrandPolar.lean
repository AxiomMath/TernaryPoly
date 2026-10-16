module

public import TernaryPeriodPolynomials.BoundaryComparison.RealEntry.PolarPointwise

@[expose] public section


/-! Combines the pointwise polar identities from `PolarPointwise.lean` into the single rewrite
`entryIntegrand n (ρ sin θ, ρ cos θ) = (scalar) * angularIntegrand n r θ`, used in clause (iii)
of `real_constant_term_entry` (Appendix C.5). -/


namespace TernaryPeriodPolynomials.Argument

/-- Rewrite `entryIntegrand`'s two integer-power (`zpow`) factors as ordinary natural-number
powers of inverses, to avoid mixing `zpow`/`pow` in later algebra. -/
theorem entryIntegrand_eq_pow (n : ℕ) (st : ℝ × ℝ) :
    entryIntegrand n st =
      (entryRadius st : ℂ)⁻¹ ^ 3 * (entryTau st + Complex.I)⁻¹ ^ (n + 3) *
        entryCoefficient st ^ n := by
  unfold entryIntegrand
  rw [show (-3 : ℤ) = -((3 : ℕ) : ℤ) from by norm_num, zpow_neg, zpow_natCast, inv_pow,
    show (-((n : ℤ) + 3)) = -((n + 3 : ℕ) : ℤ) from by push_cast; ring, zpow_neg, zpow_natCast,
    inv_pow]

/-- `exp(-(Iθ))` raised to the `(n+3)`-th power equals `exp(-(I(n+3)θ))`. -/
theorem exp_neg_I_theta_pow (n : ℕ) (θ : ℝ) :
    Complex.exp (-(Complex.I * θ)) ^ (n + 3) =
      Complex.exp (-(Complex.I * ((n : ℂ) + 3) * θ)) := by
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- The pointwise polar rewrite of `entryIntegrand`: at `(ρ sin θ, ρ cos θ)` it equals a scalar
multiple of `angularIntegrand n r θ`, for any `r` with `r² = 1+ρ²`, `r > 0`. -/
theorem entryIntegrand_polar (n : ℕ) (ρ θ r : ℝ) (hr2 : r ^ 2 = 1 + ρ ^ 2) (hr : 0 < r) :
    entryIntegrand n (ρ * Real.sin θ, ρ * Real.cos θ) =
      (-1 : ℂ) ^ n * (r : ℂ)⁻¹ ^ 3 / (Complex.I ^ (n + 3) * ((r : ℂ) + 1) ^ (n + 3)) *
        angularIntegrand n r θ := by
  rw [entryIntegrand_eq_pow, entryRadius_polar ρ θ r hr2 hr, entryTau_add_I_polar ρ θ r hr2 hr,
    entryCoefficient_polar ρ θ r hr2 hr]
  unfold angularIntegrand
  simp only [inv_div, div_pow, mul_pow, exp_neg_I_theta_pow]
  have hD : (Real.cos θ : ℂ) - Complex.I * (r : ℂ) * (Real.sin θ : ℂ) ≠ 0 :=
    c_sub_I_r_v_ne_zero r θ hr.ne'
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hr1 : (r : ℂ) + 1 ≠ 0 := by
    have h : (0 : ℝ) < r + 1 := by linarith
    exact_mod_cast h.ne'
  have hexpne : Complex.exp (-(Complex.I * ((n : ℂ) + 3) * θ)) ≠ 0 := Complex.exp_ne_zero _
  have hexpmul : Complex.exp (Complex.I * ((n : ℂ) + 3) * θ) *
      Complex.exp (-(Complex.I * ((n : ℂ) + 3) * θ)) = 1 := by
    rw [← Complex.exp_add]
    norm_num
  rw [pow_add, neg_pow]
  field_simp
  have hD' : (Real.cos θ : ℂ) - (r : ℂ) * Complex.I * (Real.sin θ : ℂ) ≠ 0 := by
    rw [mul_comm (r : ℂ) Complex.I]; exact hD
  rw [div_eq_iff (pow_ne_zero n hD')]
  linear_combination
    (-(((Real.cos θ : ℂ) - (r : ℂ) * Complex.I * (Real.sin θ : ℂ)) ^ 3 *
        ((Real.cos θ : ℂ) - (r : ℂ) * Complex.I * (Real.sin θ : ℂ)) ^ n *
        (((r : ℂ) * (Real.cos θ : ℂ) - Complex.I * (Real.sin θ : ℂ)) / (r : ℂ)) ^ n)) *
      hexpmul

end TernaryPeriodPolynomials.Argument
