module

public import TernaryPeriodPolynomials.BoundaryComparison.RealEntry.AngularExp

@[expose] public section


/-! Pointwise polar-coordinate identities for `entryRadius`, `entryTau`, `entryCoefficient`,
used (clause (iii) of `real_constant_term_entry`, Appendix C.5) to rewrite
`entryIntegrand n (ρ sin θ, ρ cos θ)` as a scalar multiple of `angularIntegrand n r θ` for
`r = √(1+ρ²)`. -/


namespace TernaryPeriodPolynomials.Argument

/-- `entryRadius` at the polar point `(ρ sin θ, ρ cos θ)` equals any `r` with `r² = 1+ρ²`,
`r > 0`. -/
theorem entryRadius_polar (ρ θ r : ℝ) (hr2 : r ^ 2 = 1 + ρ ^ 2) (hr : 0 < r) :
    entryRadius (ρ * Real.sin θ, ρ * Real.cos θ) = r := by
  unfold entryRadius
  have heq : 1 + (ρ * Real.sin θ) ^ 2 + (ρ * Real.cos θ) ^ 2 = r ^ 2 := by
    rw [hr2]; linear_combination ρ ^ 2 * Real.sin_sq_add_cos_sq θ
  rw [heq, Real.sqrt_sq hr.le]

/-- `cos θ - I r sin θ ≠ 0` whenever `r ≠ 0`. -/
theorem c_sub_I_r_v_ne_zero (r θ : ℝ) (hr : r ≠ 0) :
    (Real.cos θ : ℂ) - Complex.I * (r : ℂ) * (Real.sin θ : ℂ) ≠ 0 := by
  have hpos : (0 : ℝ) < Real.cos θ ^ 2 + r ^ 2 * Real.sin θ ^ 2 := by
    rcases eq_or_ne (Real.sin θ) 0 with hv | hv
    · have hc2 : Real.cos θ ^ 2 = 1 := by
        have h := Real.sin_sq_add_cos_sq θ
        rw [hv] at h; nlinarith [h]
      rw [hv]; nlinarith [hc2]
    · have hv2 : 0 < Real.sin θ ^ 2 := sq_pos_of_ne_zero hv
      have hr2 : 0 < r ^ 2 := sq_pos_of_ne_zero hr
      nlinarith [mul_pos hr2 hv2, sq_nonneg (Real.cos θ)]
  have key : (Complex.I * (r : ℂ) * (Real.sin θ : ℂ)) ^ 2 =
      -((r : ℂ) ^ 2 * (Real.sin θ : ℂ) ^ 2) := by
    have h2 : (Complex.I * (r : ℂ) * (Real.sin θ : ℂ)) ^ 2 =
        Complex.I ^ 2 * (r : ℂ) ^ 2 * (Real.sin θ : ℂ) ^ 2 := by ring
    rw [h2, Complex.I_sq]; ring
  have expand : ((Real.cos θ : ℂ) - Complex.I * (r : ℂ) * (Real.sin θ : ℂ)) *
      ((Real.cos θ : ℂ) + Complex.I * (r : ℂ) * (Real.sin θ : ℂ)) =
      (Real.cos θ : ℂ) ^ 2 - (Complex.I * (r : ℂ) * (Real.sin θ : ℂ)) ^ 2 := by ring
  have hprod : ((Real.cos θ : ℂ) - Complex.I * (r : ℂ) * (Real.sin θ : ℂ)) *
      ((Real.cos θ : ℂ) + Complex.I * (r : ℂ) * (Real.sin θ : ℂ)) =
      ((Real.cos θ ^ 2 + r ^ 2 * Real.sin θ ^ 2 : ℝ) : ℂ) := by
    rw [expand, key]; push_cast; ring
  intro hcontra
  rw [hcontra, zero_mul] at hprod
  have hne : ((Real.cos θ ^ 2 + r ^ 2 * Real.sin θ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hpos.ne'
  exact hne hprod.symm

/-- `cos θ - I sin θ = exp(-Iθ)` (Euler's formula, specialized to `a = 1` in
`cos_sub_I_mul_mul_sin_eq`). -/
theorem cos_sub_I_mul_sin_eq_exp (θ : ℝ) :
    (Real.cos θ : ℂ) - Complex.I * (Real.sin θ : ℂ) = Complex.exp (-(Complex.I * θ)) := by
  have h := cos_sub_I_mul_mul_sin_eq 1 θ
  push_cast at h ⊢
  linear_combination h

/-- `entryTau` at the polar point `(ρ sin θ, ρ cos θ)`, for `r` with `r² = 1+ρ²`, `r > 0`. -/
theorem entryTau_polar (ρ θ r : ℝ) (hr2 : r ^ 2 = 1 + ρ ^ 2) (hr : 0 < r) :
    entryTau (ρ * Real.sin θ, ρ * Real.cos θ) =
      (Complex.I * (r : ℂ) * (Real.cos θ : ℂ) + (Real.sin θ : ℂ)) /
        ((Real.cos θ : ℂ) - Complex.I * (r : ℂ) * (Real.sin θ : ℂ)) := by
  unfold entryTau
  rw [entryRadius_polar ρ θ r hr2 hr]
  have hden1 : ((1 + (ρ * Real.sin θ) ^ 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (by positivity : (1 + (ρ * Real.sin θ) ^ 2 : ℝ) ≠ 0)
  have hden2 : (Real.cos θ : ℂ) - Complex.I * (r : ℂ) * (Real.sin θ : ℂ) ≠ 0 :=
    c_sub_I_r_v_ne_zero r θ hr.ne'
  rw [div_eq_div_iff hden1 hden2]
  have hr2' : (r : ℂ) ^ 2 = 1 + (ρ : ℂ) ^ 2 := by exact_mod_cast hr2
  have hpyth : Complex.sin (θ : ℂ) ^ 2 + Complex.cos (θ : ℂ) ^ 2 = 1 := by
    exact_mod_cast Real.sin_sq_add_cos_sq θ
  push_cast
  linear_combination Complex.sin (θ : ℂ) * hr2' - (ρ : ℂ) ^ 2 * Complex.sin (θ : ℂ) * hpyth -
    (r : ℂ) ^ 2 * Complex.sin (θ : ℂ) * Complex.I_sq

/-- `entryCoefficient` at the polar point `(ρ sin θ, ρ cos θ)`, for `r` with `r² = 1+ρ²`,
`r > 0`. -/
theorem entryCoefficient_polar (ρ θ r : ℝ) (hr2 : r ^ 2 = 1 + ρ ^ 2) (hr : 0 < r) :
    entryCoefficient (ρ * Real.sin θ, ρ * Real.cos θ) =
      -((Real.cos θ : ℂ) - Complex.I * (Real.sin θ : ℂ) / (r : ℂ)) /
        ((Real.cos θ : ℂ) - Complex.I * (r : ℂ) * (Real.sin θ : ℂ)) := by
  unfold entryCoefficient
  rw [entryRadius_polar ρ θ r hr2 hr]
  have hden1 : ((1 + (ρ * Real.sin θ) ^ 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (by positivity : (1 + (ρ * Real.sin θ) ^ 2 : ℝ) ≠ 0)
  have hden2 : (Real.cos θ : ℂ) - Complex.I * (r : ℂ) * (Real.sin θ : ℂ) ≠ 0 :=
    c_sub_I_r_v_ne_zero r θ hr.ne'
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  rw [div_eq_div_iff hden1 hden2]
  have hr2' : (r : ℂ) ^ 2 = 1 + (ρ : ℂ) ^ 2 := by exact_mod_cast hr2
  have hpyth : Complex.sin (θ : ℂ) ^ 2 + Complex.cos (θ : ℂ) ^ 2 = 1 := by
    exact_mod_cast Real.sin_sq_add_cos_sq θ
  push_cast
  field_simp
  linear_combination (Complex.I * Complex.sin (θ : ℂ)) * hr2' -
    (Complex.I * (ρ : ℂ) ^ 2 * Complex.sin (θ : ℂ)) * hpyth +
    ((ρ : ℂ) ^ 2 * Complex.sin (θ : ℂ) ^ 2 * Complex.cos (θ : ℂ) * (r : ℂ)) * Complex.I_sq

/-- `entryTau (ρ sin θ, ρ cos θ) + I = I(r+1) e^{-iθ} / (cos θ - I r sin θ)`. -/
theorem entryTau_add_I_polar (ρ θ r : ℝ) (hr2 : r ^ 2 = 1 + ρ ^ 2) (hr : 0 < r) :
    entryTau (ρ * Real.sin θ, ρ * Real.cos θ) + Complex.I =
      Complex.I * ((r : ℂ) + 1) * Complex.exp (-(Complex.I * θ)) /
        ((Real.cos θ : ℂ) - Complex.I * (r : ℂ) * (Real.sin θ : ℂ)) := by
  rw [entryTau_polar ρ θ r hr2 hr, ← cos_sub_I_mul_sin_eq_exp]
  have hden2 : (Real.cos θ : ℂ) - Complex.I * (r : ℂ) * (Real.sin θ : ℂ) ≠ 0 :=
    c_sub_I_r_v_ne_zero r θ hr.ne'
  field_simp
  linear_combination (Real.sin θ : ℂ) * Complex.I_sq

end TernaryPeriodPolynomials.Argument
