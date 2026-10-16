module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Euler.Series

@[expose] public section


noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem quadraticRecurrence_tsum_mul_factor_general
    (coefficients : ℕ → ℂ) (trace determinant : ℂ)
    (recurrence : ∀ exponent,
      coefficients (exponent + 2) = trace * coefficients (exponent + 1) -
        determinant * coefficients exponent)
    (summable : Summable coefficients) :
    (1 - trace + determinant) * (∑' exponent, coefficients exponent) =
      coefficients 0 + coefficients 1 - trace * coefficients 0 := by
  have successor_summable : Summable (fun exponent => coefficients (exponent + 1)) :=
    (summable_nat_add_iff 1).mpr summable
  have initial_sum := summable.tsum_eq_zero_add
  have successor_sum := successor_summable.tsum_eq_zero_add
  have recurrence_sum :
      (∑' exponent, coefficients (exponent + 2)) =
        trace * (∑' exponent, coefficients (exponent + 1)) -
          determinant * (∑' exponent, coefficients exponent) := by
    simp_rw [recurrence]
    rw [(successor_summable.mul_left trace).tsum_sub
      (summable.mul_left determinant), successor_summable.tsum_mul_left,
      summable.tsum_mul_left]
  simp only [Nat.add_assoc] at successor_sum
  rw [recurrence_sum] at successor_sum
  linear_combination (1 - trace) * initial_sum + successor_sum

theorem quadraticRecurrence_weighted_tsum_mul_factor_general
    (coefficients : ℕ → ℂ) (trace determinant scale : ℂ)
    (recurrence : ∀ exponent,
      coefficients (exponent + 2) = trace * coefficients (exponent + 1) -
        determinant * coefficients exponent)
    (summable : Summable (fun exponent => coefficients exponent * scale ^ exponent)) :
    (1 - trace * scale + determinant * scale ^ 2) *
        (∑' exponent, coefficients exponent * scale ^ exponent) =
      coefficients 0 + (coefficients 1 - trace * coefficients 0) * scale := by
  have identity := quadraticRecurrence_tsum_mul_factor_general
    (fun exponent => coefficients exponent * scale ^ exponent)
    (trace * scale) (determinant * scale ^ 2) (fun exponent => by
      rw [recurrence, pow_add, pow_succ]
      ring) summable
  simp only [pow_zero, mul_one, pow_one] at identity
  linear_combination identity

end TernaryPeriodPolynomials.SphericalDetection.Helpers
