module

public import TernaryPeriodPolynomials.BoundaryComparison.RealEntry.PeriodicityBridge
public import TernaryPeriodPolynomials.BoundaryComparison.RealEntry.RadialIntegral
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.Bochner.Set

@[expose] public section


/-! Clause (iii) of `real_constant_term_entry` (Appendix C.5): evaluate `entryIntegral n` via the
Fubini split (`FubiniSplit.lean`), the inner `θ`-integral closed form (`PeriodicityBridge.lean`),
and the radial integral (`RadialIntegral.lean`), then divide by the stated normalization. -/


open MeasureTheory Set

namespace TernaryPeriodPolynomials.Argument

/-- The inner `θ`-integral closed form (`inner_theta_integral`), rewritten by cancelling the
shared factor `(√(1+ρ²)+1)^(n+3)` between numerator and denominator, as a constant (independent
of `ρ`) times the real-cast radial weight `ρ(√(1+ρ²))⁻¹^(n+3)`. -/
theorem inner_theta_integral_eq_coeff_mul_radial (n : ℕ) (ρ : ℝ) (hρ : 0 < ρ) :
    (∫ θ in Set.Ioo (-Real.pi) Real.pi, ρ • entryIntegrand n (ρ * Real.sin θ, ρ * Real.cos θ)) =
      ((-1 : ℂ) ^ n * (2 * (Real.pi : ℂ)) / (Complex.I ^ (n + 3) * (2 : ℂ) ^ (n + 3))) *
        ((ρ * (Real.sqrt (1 + ρ ^ 2))⁻¹ ^ (n + 3) : ℝ) : ℂ) := by
  rw [inner_theta_integral n ρ hρ]
  have hr : 0 < Real.sqrt (1 + ρ ^ 2) := Real.sqrt_pos.mpr (by positivity)
  set r : ℝ := Real.sqrt (1 + ρ ^ 2) with hr_def
  have hrc0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hrc1 : (r : ℂ) + 1 ≠ 0 := by
    intro hc
    have hc' : ((r + 1 : ℝ) : ℂ) = 0 := by push_cast; exact hc
    rw [Complex.ofReal_eq_zero] at hc'
    linarith
  have hI : (Complex.I : ℂ) ^ (n + 3) ≠ 0 := pow_ne_zero _ Complex.I_ne_zero
  have h2 : (2 : ℂ) ^ (n + 3) ≠ 0 := pow_ne_zero _ two_ne_zero
  have hrn : (r : ℂ) ^ n ≠ 0 := pow_ne_zero _ hrc0
  have hrn3 : (r : ℂ) ^ (n + 3) ≠ 0 := pow_ne_zero _ hrc0
  have hr13 : ((r : ℂ) + 1) ^ (n + 3) ≠ 0 := pow_ne_zero _ hrc1
  have hcast2 : ((ρ * r⁻¹ ^ (n + 3) : ℝ) : ℂ) = (ρ : ℂ) * ((r : ℂ) ^ (n + 3))⁻¹ := by
    push_cast
    rw [inv_pow]
  rw [hcast2, inv_pow]
  field_simp
  try ring

/-- `entryIntegral n` evaluated via the Fubini split, the inner `θ`-integral closed form, and the
radial integral. -/
theorem entryIntegral_eq_value (n : ℕ) :
    entryIntegral n =
      -Complex.I * (((-1 : ℂ) ^ n * (2 * (Real.pi : ℂ)) /
          (Complex.I ^ (n + 3) * (2 : ℂ) ^ (n + 3))) * ((1 / ((n : ℝ) + 1) : ℝ) : ℂ)) := by
  have hcast3 : (∫ a in Set.Ioi (0 : ℝ),
        ((a * (Real.sqrt (1 + a ^ 2))⁻¹ ^ (n + 3) : ℝ) : ℂ)) =
      ((∫ a in Set.Ioi (0 : ℝ), a * (Real.sqrt (1 + a ^ 2))⁻¹ ^ (n + 3) : ℝ) : ℂ) :=
    integral_ofReal
  unfold entryIntegral
  rw [entryIntegrand_integral_eq_iterated,
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      (fun ρ hρ => inner_theta_integral_eq_coeff_mul_radial n ρ hρ),
    MeasureTheory.integral_const_mul, hcast3, radial_integral]

/-- Clause (iii) of `real_constant_term_entry`: dividing `entryIntegral n` by its value
`(-1)ⁿ(2i)^{-(n+3)}` at `τ = i` gives `-2πi/(n+1)`. -/
theorem real_constant_term_entry_clause3 (n : ℕ) :
    entryIntegral n / ((-1) ^ n * (2 * Complex.I) ^ (-((n : ℤ) + 3))) =
      -2 * Real.pi * Complex.I / ((n : ℂ) + 1) := by
  rw [entryIntegral_eq_value n]
  have hn1 : ((n : ℂ) + 1) ≠ 0 := by
    intro hc
    have hc' : (((n : ℝ) + 1 : ℝ) : ℂ) = 0 := by push_cast; exact hc
    rw [Complex.ofReal_eq_zero] at hc'
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hcast : ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) = 1 / ((n : ℂ) + 1) := by
    push_cast
    ring
  rw [hcast]
  have hI : (Complex.I : ℂ) ^ (n + 3) ≠ 0 := pow_ne_zero _ Complex.I_ne_zero
  have h2 : (2 : ℂ) ^ (n + 3) ≠ 0 := pow_ne_zero _ two_ne_zero
  have hm1 : ((-1 : ℂ)) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  have hzpow :
      (2 * Complex.I) ^ (-((n : ℤ) + 3)) = ((2 : ℂ) ^ (n + 3) * Complex.I ^ (n + 3))⁻¹ := by
    rw [show (-((n : ℤ) + 3)) = -((n + 3 : ℕ) : ℤ) from by push_cast; ring, zpow_neg,
      zpow_natCast, mul_pow]
  rw [hzpow]
  field_simp

end TernaryPeriodPolynomials.Argument
