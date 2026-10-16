module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Padic.PlaneIntegrability

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def padicNormPowerWeight (exponent : ℂ) (radius : ℝ) : ℂ :=
  Complex.exp (exponent * (Real.log radius : ℂ))

theorem padicNormPowerWeight_one (exponent : ℂ) : padicNormPowerWeight exponent 1 = 1 := by
  simp only [padicNormPowerWeight, Real.log_one, Complex.ofReal_zero, mul_zero, Complex.exp_zero]

theorem padicNormPowerWeight_norm (exponent : ℂ) (radius : ℝ) :
    ‖padicNormPowerWeight exponent radius‖ = Real.exp (exponent.re * Real.log radius) := by
  simp only [padicNormPowerWeight, Complex.norm_exp, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]

theorem padicNormPowerWeight_geometric (prime : ℕ) (positive : 0 < prime) (exponent : ℂ) (power : ℕ) :
    ((prime : ℝ) ^ power) * ((prime : ℝ) ^ power) * ‖padicNormPowerWeight exponent ((prime : ℝ) ^ power)⁻¹‖ =
      (Real.exp ((2 - exponent.re) * Real.log prime)) ^ power := by
  have positive_real : (0 : ℝ) < prime := by exact_mod_cast positive
  have power_exp : (prime : ℝ) ^ power = Real.exp ((power : ℝ) * Real.log prime) := by
    rw [Real.exp_nat_mul, Real.exp_log positive_real]
  rw [padicNormPowerWeight_norm, Real.log_inv, Real.log_pow, power_exp,
    ← Real.exp_add, ← Real.exp_add, ← Real.exp_nat_mul]
  congr 1
  ring

theorem padicNormPowerWeight_summable (prime : ℕ) (prime_large : 1 < prime)
    (exponent : ℂ) (convergent : 2 < exponent.re) :
    Summable (fun power : ℕ => ((prime : ℝ) ^ power) * ((prime : ℝ) ^ power) *
      ‖padicNormPowerWeight exponent ((prime : ℝ) ^ power)⁻¹‖) := by
  simp_rw [padicNormPowerWeight_geometric prime (by omega) exponent]
  apply summable_geometric_of_norm_lt_one
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_lt_one_iff]
  exact mul_neg_of_neg_of_pos (by linarith) (Real.log_pos (by exact_mod_cast prime_large))

theorem padicNormPowerWeight_integrable {prime : ℕ} [Fact prime.Prime]
    [MeasurableSpace ℚ_[prime]] [BorelSpace ℚ_[prime]]
    (measure : Measure ℚ_[prime]) [measure.IsAddHaarMeasure]
    (normalized : measure {value : ℚ_[prime] | ‖value‖ ≤ 1} = 1)
    (exponent : ℂ) (convergent : 2 < exponent.re) (value : GeneralLinearGroup (Fin 2) ℚ_[prime] → ℂ)
    (fixed : ∀ matrix compact, value (matrix * GeneralLinearGroup.map PadicInt.Coe.ringHom compact) = value matrix)
    (bounded : ∃ bound : ℝ, ∀ matrix, ‖value matrix‖ ≤ bound) :
    Integrable (padicPlaneWeightedValue (padicNormPowerWeight exponent) value) (measure.prod measure) :=
  padicPlaneWeightedValue_integrable_of_summable measure normalized (padicNormPowerWeight exponent)
    value fixed bounded (padicNormPowerWeight_summable prime (Nat.Prime.one_lt Fact.out) exponent convergent)

end TernaryPeriodPolynomials.SphericalDetection.Helpers
