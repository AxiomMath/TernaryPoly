module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.QuadraticSeriesInitialValues

@[expose] public section


noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem sphereRecurrence_shell_tsum_mul_factor (coefficients : ℕ → ℂ)
    (prime trace central scale : ℂ) (nonzero : prime ≠ 0)
    (first : coefficients 1 = trace * coefficients 0)
    (second : coefficients 2 = (trace ^ 2 - (prime + 1) * central) * coefficients 0)
    (recurrence : ∀ power, coefficients (power + 3) =
      trace * coefficients (power + 2) - prime * central * coefficients (power + 1))
    (summable : Summable (fun power =>
      (1 - prime⁻¹) * coefficients (power + 1) * scale ^ (power + 1))) :
    (1 - trace * scale + prime * central * scale ^ 2) *
        (coefficients 0 + ∑' power, (1 - prime⁻¹) * coefficients (power + 1) * scale ^ (power + 1)) =
      (1 - trace / prime * scale + central / prime * scale ^ 2) * coefficients 0 := by
  have step (power : ℕ) :
      (1 - prime⁻¹) * coefficients (power + 2 + 1) * scale ^ (power + 2 + 1) =
        (trace * scale) * ((1 - prime⁻¹) * coefficients (power + 1 + 1) * scale ^ (power + 1 + 1)) -
          (prime * central * scale ^ 2) * ((1 - prime⁻¹) * coefficients (power + 1) * scale ^ (power + 1)) := by
    simp only [Nat.add_assoc, recurrence, pow_add, pow_one]
    ring
  have identity := quadraticRecurrence_tsum_mul_factor_general
    (fun power => (1 - prime⁻¹) * coefficients (power + 1) * scale ^ (power + 1))
    (trace * scale) (prime * central * scale ^ 2) step summable
  rw [mul_add, identity]
  simp only [Nat.zero_add, Nat.reduceAdd, first, second, pow_one]
  field_simp
  ring

end TernaryPeriodPolynomials.SphericalDetection.Helpers
