module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Cusp.PadicSphereValues

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped ENNReal

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def padicPrimitiveSeriesScale (prime : ℕ) (exponent : ℂ) : ℂ :=
  (prime : ℂ) * Complex.exp (-exponent * (Real.log prime : ℂ))

theorem padicNormPowerWeight_inverse_power (prime power : ℕ) (exponent : ℂ) :
    padicNormPowerWeight exponent ((prime : ℝ) ^ power)⁻¹ =
      Complex.exp (-exponent * (Real.log prime : ℂ)) ^ power := by
  rw [padicNormPowerWeight, Real.log_inv, Real.log_pow, Complex.ofReal_neg,
    Complex.ofReal_mul, Complex.ofReal_natCast, ← Complex.exp_nat_mul]
  congr 1
  ring

theorem padicPrimitiveShell_toReal (prime : ℕ) (positive : 0 < prime) (power : ℕ) :
    ((((prime ^ (power + 1) : ℕ) : ℝ≥0∞) - ((prime ^ power : ℕ) : ℝ≥0∞)).toReal) =
      (prime : ℝ) ^ (power + 1) - (prime : ℝ) ^ power := by
  have increasing : prime ^ power ≤ prime ^ (power + 1) := by
    rw [pow_succ]
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (prime ^ power) (Nat.one_le_iff_ne_zero.mpr (by omega))
  rw [ENNReal.toReal_sub_of_le (by exact_mod_cast increasing) (by norm_num)]
  simp only [Nat.cast_pow, ENNReal.toReal_pow, ENNReal.toReal_natCast]

theorem padicPrimitiveSeriesTerm_geometric {prime : ℕ} [Fact prime.Prime]
    (exponent : ℂ) (value : GeneralLinearGroup (Fin 2) ℚ_[prime] → ℂ) (power : ℕ) :
    padicPrimitiveSeriesTerm (padicNormPowerWeight exponent) value power =
      (1 - (prime : ℂ)⁻¹) * padicPrimitiveSum (power + 1) value *
        padicPrimitiveSeriesScale prime exponent ^ (power + 1) := by
  have nonzero : (prime : ℂ) ≠ 0 := by exact_mod_cast Nat.Prime.ne_zero Fact.out
  rw [padicPrimitiveSeriesTerm, padicPrimitiveShell_toReal prime (Nat.Prime.pos Fact.out),
    padicNormPowerWeight_inverse_power, Complex.real_smul, Complex.ofReal_sub,
    Complex.ofReal_pow, Complex.ofReal_pow, Complex.ofReal_natCast,
    padicPrimitiveSeriesScale, mul_pow, pow_succ]
  field_simp

theorem cuspLocalPadicSeriesTerm_geometric (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (base : BinaryFiniteGL) (place : FinitePlace) (exponent : ℂ) (power : ℕ) :
    letI : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
      ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
    padicPrimitiveSeriesTerm (padicNormPowerWeight exponent) (cuspLocalPadicValue cusp vector base place) power =
      (1 - ((Rat.HeightOneSpectrum.primesEquiv place).val : ℂ)⁻¹) *
        cuspLocalPadicSphereValue cusp vector base place (power + 1) *
          padicPrimitiveSeriesScale (Rat.HeightOneSpectrum.primesEquiv place).val exponent ^ (power + 1) := by
  let : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
  rw [padicPrimitiveSeriesTerm_geometric, ← cuspLocalPadicPrimitiveOperator_realize]
  rfl

end TernaryPeriodPolynomials.SphericalDetection.Helpers
