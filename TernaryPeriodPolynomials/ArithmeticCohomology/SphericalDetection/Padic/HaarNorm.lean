module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Padic.HaarScaling

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory
open scoped ENNReal NNReal

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem padicHaarChar_integral {prime : ℕ} [Fact prime.Prime]
    [MeasurableSpace ℚ_[prime]] [BorelSpace ℚ_[prime]]
    (measure : Measure ℚ_[prime]) [measure.IsAddHaarMeasure]
    (normalized : measure {value : ℚ_[prime] | ‖value‖ ≤ 1} = 1)
    (unit : ℚ_[prime]ˣ) (integral : ‖unit.val‖ ≤ 1) :
    (addEquivAddHaarChar (ContinuousAddEquiv.mulLeft unit) : ℝ) = ‖unit.val‖ := by
  have nonnegative := (Padic.norm_le_one_iff_val_nonneg unit.val).mp integral
  have cast : ((unit.val.valuation.toNat : ℕ) : ℤ) = unit.val.valuation :=
    Int.toNat_of_nonneg nonnegative
  have norm_power : ‖unit.val‖ = ‖(prime : ℚ_[prime]) ^ unit.val.valuation.toNat‖ := by
    conv_lhs => rw [Padic.norm_eq_zpow_neg_valuation unit.ne_zero, ← cast, zpow_neg, zpow_natCast]
    rw [norm_pow, Padic.norm_p, inv_pow]
  have equality := congrArg ENNReal.toReal
    (padicHaarChar_primePower measure normalized unit.val.valuation.toNat unit norm_power)
  rw [norm_power, norm_pow, Padic.norm_p, inv_pow]
  simpa only [ENNReal.coe_toReal, ENNReal.toReal_inv, ENNReal.toReal_natCast, Nat.cast_pow,
    ENNReal.toReal_pow] using equality

theorem padicHaarChar_eq_norm {prime : ℕ} [Fact prime.Prime]
    [MeasurableSpace ℚ_[prime]] [BorelSpace ℚ_[prime]]
    (measure : Measure ℚ_[prime]) [measure.IsAddHaarMeasure]
    (normalized : measure {value : ℚ_[prime] | ‖value‖ ≤ 1} = 1) (unit : ℚ_[prime]ˣ) :
    (addEquivAddHaarChar (ContinuousAddEquiv.mulLeft unit) : ℝ) = ‖unit.val‖ := by
  by_cases integral : ‖unit.val‖ ≤ 1
  · exact padicHaarChar_integral measure normalized unit integral
  · have inverse_integral : ‖(unit⁻¹).val‖ ≤ 1 := by
      rw [Units.val_inv_eq_inv_val, norm_inv]
      exact inv_le_one_of_one_le₀ (le_of_lt (lt_of_not_ge integral))
    have equality := padicHaarChar_integral measure normalized unit⁻¹ inverse_integral
    have inverse_equiv : ContinuousAddEquiv.mulLeft unit⁻¹ = (ContinuousAddEquiv.mulLeft unit).symm := by
      ext value
      rfl
    rw [inverse_equiv, addEquivAddHaarChar_symm, NNReal.coe_inv, Units.val_inv_eq_inv_val, norm_inv] at equality
    exact inv_injective equality

theorem padicHaarChar_ball_measure {prime : ℕ} [Fact prime.Prime]
    [MeasurableSpace ℚ_[prime]] [BorelSpace ℚ_[prime]]
    (measure : Measure ℚ_[prime]) [measure.IsAddHaarMeasure]
    (normalized : measure {value : ℚ_[prime] | ‖value‖ ≤ 1} = 1) (unit : ℚ_[prime]ˣ) :
    measure {value : ℚ_[prime] | ‖unit.val * value‖ ≤ 1} =
      (addEquivAddHaarChar (ContinuousAddEquiv.mulLeft unit) : ℝ≥0∞)⁻¹ := by
  have scaling := addEquivAddHaarChar_smul_preimage measure
    (X := {value : ℚ_[prime] | ‖value‖ ≤ 1}) (ContinuousAddEquiv.mulLeft unit)
  rw [normalized] at scaling
  change (addEquivAddHaarChar (ContinuousAddEquiv.mulLeft unit) : ℝ≥0∞) *
    measure {value : ℚ_[prime] | ‖unit.val * value‖ ≤ 1} = 1 at scaling
  exact ENNReal.eq_inv_of_mul_eq_one_left ((mul_comm _ _).trans scaling)

end TernaryPeriodPolynomials.SphericalDetection.Helpers
