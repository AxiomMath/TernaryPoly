module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Padic.PrimitiveGeometric

@[expose] public section


noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem padicPrimitiveSeriesScale_norm (prime : ℕ) (positive : 0 < prime) (exponent : ℂ) :
    ‖padicPrimitiveSeriesScale prime exponent‖ = Real.exp ((1 - exponent.re) * Real.log prime) := by
  have positive_real : (0 : ℝ) < prime := by exact_mod_cast positive
  simp only [padicPrimitiveSeriesScale, norm_mul, Complex.norm_natCast, Complex.norm_exp,
    Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero]
  calc
    (prime : ℝ) * Real.exp (-exponent.re * Real.log prime) =
        Real.exp (Real.log prime) * Real.exp (-exponent.re * Real.log prime) := by
      rw [Real.exp_log positive_real]
    _ = _ := by
      rw [← Real.exp_add]
      congr 1
      ring

theorem padicPrimitiveSeriesScale_norm_lt_one (prime : ℕ) (large : 1 < prime)
    (exponent : ℂ) (convergent : 1 < exponent.re) : ‖padicPrimitiveSeriesScale prime exponent‖ < 1 := by
  rw [padicPrimitiveSeriesScale_norm prime (by omega), Real.exp_lt_one_iff]
  exact mul_neg_of_neg_of_pos (by linarith) (Real.log_pos (by exact_mod_cast large))

theorem padicPrimitiveSeriesScale_add_one (prime : ℕ) (positive : 0 < prime) (exponent : ℂ) :
    padicPrimitiveSeriesScale prime (exponent + 1) = padicPrimitiveSeriesScale prime exponent / prime := by
  have positive_real : (0 : ℝ) < prime := by exact_mod_cast positive
  have exponential : Complex.exp (Real.log prime : ℂ) = (prime : ℂ) := by
    rw [← Complex.ofReal_exp, Real.exp_log positive_real, Complex.ofReal_natCast]
  have split : -(exponent + 1) * (Real.log prime : ℂ) =
      -exponent * (Real.log prime : ℂ) + -(Real.log prime : ℂ) := by ring
  simp only [padicPrimitiveSeriesScale, split, Complex.exp_add, Complex.exp_neg, exponential, div_eq_mul_inv]
  ring

end TernaryPeriodPolynomials.SphericalDetection.Helpers
