module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Padic.SeriesScaleNorm

@[expose] public section


noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def classicalPrimeEulerPolynomial (prime : ℕ) (weight : ℤ) (trace argument : ℂ) : ℂ :=
  1 - trace * (prime : ℂ) ^ (-argument) + (prime : ℂ) ^ (weight - 1) * ((prime : ℂ) ^ (-argument)) ^ 2

theorem padicPrimitiveSeriesScale_eq_cpow (prime : ℕ) (positive : 0 < prime) (exponent : ℂ) :
    padicPrimitiveSeriesScale prime exponent = (prime : ℂ) ^ (1 - exponent) := by
  have nonzero : (prime : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt positive)
  have logarithm : Complex.log (prime : ℂ) = (Real.log prime : ℂ) := by
    simpa only [Complex.ofReal_natCast] using (Complex.ofReal_log (show (0 : ℝ) ≤ prime by positivity)).symm
  have weight : Complex.exp (-exponent * (Real.log prime : ℂ)) = (prime : ℂ) ^ (-exponent) := by
    rw [Complex.cpow_def_of_ne_zero nonzero, logarithm]
    congr 1
    ring
  rw [padicPrimitiveSeriesScale, weight, sub_eq_add_neg, Complex.cpow_add _ _ nonzero, Complex.cpow_one]

theorem padicClassicalEuler_trace_scaling (prime : ℕ) (positive : 0 < prime)
    (halfWeight : ℤ) (trace exponent : ℂ) :
    ((prime : ℂ) ^ (halfWeight + 1) * trace) * padicPrimitiveSeriesScale prime exponent =
      trace * (prime : ℂ) ^ (-(exponent - halfWeight - 2)) := by
  have nonzero : (prime : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt positive)
  rw [padicPrimitiveSeriesScale_eq_cpow prime positive, ← Complex.cpow_intCast]
  calc
    _ = trace * ((prime : ℂ) ^ ((halfWeight + 1 : ℤ) : ℂ) * (prime : ℂ) ^ (1 - exponent)) := by ring
    _ = _ := by
      rw [← Complex.cpow_add _ _ nonzero]
      congr 2
      push_cast
      ring

theorem padicClassicalEuler_determinant_scaling (prime : ℕ) (positive : 0 < prime)
    (halfWeight : ℤ) (exponent : ℂ) :
    (prime : ℂ) * padicPrimitiveSeriesScale prime exponent ^ 2 =
      (prime : ℂ) ^ (-2 * halfWeight - 1) * ((prime : ℂ) ^ (-(exponent - halfWeight - 2))) ^ 2 := by
  have nonzero : (prime : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt positive)
  rw [padicPrimitiveSeriesScale_eq_cpow prime positive, ← Complex.cpow_intCast,
    ← Complex.cpow_mul_nat, ← Complex.cpow_mul_nat, ← Complex.cpow_add _ _ nonzero]
  calc
    _ = (prime : ℂ) ^ (1 + (1 - exponent) * (2 : ℕ)) := by
      rw [Complex.cpow_add _ _ nonzero, Complex.cpow_one]
    _ = _ := by
      congr 1
      push_cast
      ring

theorem padicClassicalEuler_polynomial_scaling (prime : ℕ) (positive : 0 < prime)
    (halfWeight : ℤ) (trace exponent : ℂ) :
    1 - ((prime : ℂ) ^ (halfWeight + 1) * trace) * padicPrimitiveSeriesScale prime exponent +
        (prime : ℂ) * padicPrimitiveSeriesScale prime exponent ^ 2 =
      classicalPrimeEulerPolynomial prime (-2 * halfWeight) trace (exponent - halfWeight - 2) := by
  rw [padicClassicalEuler_trace_scaling prime positive, padicClassicalEuler_determinant_scaling prime positive halfWeight]
  rfl

theorem padicPrimeEulerNumerator_shift (prime : ℕ) (positive : 0 < prime) (trace central exponent : ℂ) :
    1 - trace / prime * padicPrimitiveSeriesScale prime exponent +
        central / prime * padicPrimitiveSeriesScale prime exponent ^ 2 =
      1 - trace * padicPrimitiveSeriesScale prime (exponent + 1) +
        prime * central * padicPrimitiveSeriesScale prime (exponent + 1) ^ 2 := by
  have nonzero : (prime : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt positive)
  rw [padicPrimitiveSeriesScale_add_one prime positive]
  field_simp

end TernaryPeriodPolynomials.SphericalDetection.Helpers
