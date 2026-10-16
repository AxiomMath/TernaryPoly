module

public import TernaryPeriodPolynomials.BoundaryComparison.RealEntry.FubiniSplit
public import TernaryPeriodPolynomials.BoundaryComparison.RealEntry.AngularIntegral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

@[expose] public section


/-! Evaluate the inner `θ`-integral of the Fubini-split integral (`FubiniSplit.lean`) for fixed
`ρ > 0`: rewrite pointwise via `entryIntegrand_polar`, bridge `Ioo (-π) π` to the periodic
interval `[0, 2π]` via `angularIntegrand`'s `2π`-periodicity, then apply clause (i)
(`real_constant_term_entry_clause1`). Used for clause (iii) of `real_constant_term_entry`
(Appendix C.5). -/


open MeasureTheory Set

namespace TernaryPeriodPolynomials.Argument

/-- `angularIntegrand n r` is `2π`-periodic in `θ`, since `cos`/`sin` are `2π`-periodic and
`exp(i(n+3)θ)` picks up a factor `exp(i(n+3)·2π) = 1`. -/
theorem angularIntegrand_periodic (n : ℕ) (r : ℝ) :
    Function.Periodic (angularIntegrand n r) (2 * Real.pi) := by
  intro θ
  have hexp : Complex.exp (((n : ℂ) + 3) * (2 * (Real.pi : ℂ) * Complex.I)) = 1 := by
    rw [show ((n : ℂ) + 3) * (2 * (Real.pi : ℂ) * Complex.I) =
        ((n + 3 : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) from by push_cast; ring,
      Complex.exp_nat_mul, Complex.exp_two_pi_mul_I, one_pow]
  unfold angularIntegrand
  rw [Real.cos_add_two_pi, Real.sin_add_two_pi]
  push_cast
  have hstep : Complex.I * ((n : ℂ) + 3) * (θ + 2 * Real.pi) =
      Complex.I * ((n : ℂ) + 3) * θ + ((n : ℂ) + 3) * (2 * (Real.pi : ℂ) * Complex.I) := by
    ring
  rw [hstep, Complex.exp_add, hexp, mul_one]

/-- `∫θ in Ioo (-π) π, angularIntegrand n r θ` agrees with clause (i)'s `0..2π` integral, via
`2π`-periodicity. -/
theorem angularIntegrand_Ioo_integral (n : ℕ) (r : ℝ) (hr : 0 < r) :
    (∫ θ in Set.Ioo (-Real.pi) Real.pi, angularIntegrand n r θ) =
      2 * Real.pi * ((r : ℂ) + 1) ^ (n + 3) / (2 ^ (n + 3) * (r : ℂ) ^ n) := by
  have hab : (-Real.pi) ≤ Real.pi := by linarith [Real.pi_pos]
  rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hab]
  have hper := (angularIntegrand_periodic n r).intervalIntegral_add_eq (-Real.pi) 0
  rw [show (-Real.pi + 2 * Real.pi) = Real.pi from by ring,
    show ((0 : ℝ) + 2 * Real.pi) = 2 * Real.pi from by ring] at hper
  rw [hper]
  exact real_constant_term_entry_clause1 n r hr

/-- The inner `θ`-integral of the Fubini-split integral, for fixed `ρ > 0`, evaluated via the
pointwise polar rewrite (`entryIntegrand_polar`) and `angularIntegrand_Ioo_integral`. -/
theorem inner_theta_integral (n : ℕ) (ρ : ℝ) (hρ : 0 < ρ) :
    (∫ θ in Set.Ioo (-Real.pi) Real.pi, ρ • entryIntegrand n (ρ * Real.sin θ, ρ * Real.cos θ)) =
      (ρ : ℂ) * ((-1 : ℂ) ^ n * (Real.sqrt (1 + ρ ^ 2) : ℂ)⁻¹ ^ 3 /
          (Complex.I ^ (n + 3) * ((Real.sqrt (1 + ρ ^ 2) : ℂ) + 1) ^ (n + 3))) *
        (2 * Real.pi * ((Real.sqrt (1 + ρ ^ 2) : ℂ) + 1) ^ (n + 3) /
          (2 ^ (n + 3) * (Real.sqrt (1 + ρ ^ 2) : ℂ) ^ n)) := by
  set r := Real.sqrt (1 + ρ ^ 2) with hr_def
  have hr2 : r ^ 2 = 1 + ρ ^ 2 := Real.sq_sqrt (by positivity)
  have hr : 0 < r := Real.sqrt_pos.mpr (by positivity)
  have hpt : ∀ θ : ℝ, ρ • entryIntegrand n (ρ * Real.sin θ, ρ * Real.cos θ) =
      (ρ : ℂ) * ((-1 : ℂ) ^ n * (r : ℂ)⁻¹ ^ 3 / (Complex.I ^ (n + 3) * ((r : ℂ) + 1) ^ (n + 3))) *
        angularIntegrand n r θ := by
    intro θ
    rw [Complex.real_smul, entryIntegrand_polar n ρ θ r hr2 hr]
    ring
  simp_rw [hpt, MeasureTheory.integral_const_mul]
  rw [angularIntegrand_Ioo_integral n r hr]

end TernaryPeriodPolynomials.Argument
