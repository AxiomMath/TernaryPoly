module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Padic.PivotFiberMeasure

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open scoped ENNReal NNReal

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem padicHaarChar_primePower {prime : ℕ} [Fact prime.Prime]
    [MeasurableSpace ℚ_[prime]] [BorelSpace ℚ_[prime]]
    (measure : Measure ℚ_[prime]) [measure.IsAddHaarMeasure]
    (normalized : measure {value : ℚ_[prime] | ‖value‖ ≤ 1} = 1)
    (power : ℕ) (unit : ℚ_[prime]ˣ) (same_norm : ‖unit.val‖ = ‖(prime : ℚ_[prime]) ^ power‖) :
    (addEquivAddHaarChar (ContinuousAddEquiv.mulLeft unit) : ℝ≥0∞) =
      ((prime ^ power : ℕ) : ℝ≥0∞)⁻¹ := by
  have preimage : (ContinuousAddEquiv.mulLeft unit) ⁻¹' padicPrimePowerLattice power =
      {value : ℚ_[prime] | ‖value‖ ≤ 1} := by
    ext value
    change ‖unit.val * value‖ ≤ ‖(prime : ℚ_[prime]) ^ power‖ ↔ ‖value‖ ≤ 1
    rw [norm_mul, ← same_norm]
    simpa only [mul_one] using (mul_le_mul_iff_right₀ (norm_pos_iff.mpr unit.ne_zero) :
      ‖unit.val‖ * ‖value‖ ≤ ‖unit.val‖ * 1 ↔ ‖value‖ ≤ 1)
  have scaling := addEquivAddHaarChar_smul_preimage measure (X := padicPrimePowerLattice power)
    (ContinuousAddEquiv.mulLeft unit)
  rw [preimage, normalized, padicPrimePowerLattice_measure measure normalized] at scaling
  change (addEquivAddHaarChar (ContinuousAddEquiv.mulLeft unit) : ℝ≥0∞) * 1 = _ at scaling
  simpa only [mul_one] using scaling

def padicInversePowerBall {prime : ℕ} [Fact prime.Prime] (power : ℕ) : Set ℚ_[prime] :=
  {value | ‖value‖ ≤ ‖(prime : ℚ_[prime]) ^ power‖⁻¹}

theorem padicInversePowerBall_measurable {prime : ℕ} [Fact prime.Prime]
    [MeasurableSpace ℚ_[prime]] [BorelSpace ℚ_[prime]] (power : ℕ) :
    MeasurableSet (padicInversePowerBall (prime := prime) power) :=
  (isClosed_le continuous_norm continuous_const).measurableSet

theorem padicInversePowerBall_measure {prime : ℕ} [Fact prime.Prime]
    [MeasurableSpace ℚ_[prime]] [BorelSpace ℚ_[prime]]
    (measure : Measure ℚ_[prime]) [measure.IsAddHaarMeasure]
    (normalized : measure {value : ℚ_[prime] | ‖value‖ ≤ 1} = 1) (power : ℕ) :
    measure (padicInversePowerBall (prime := prime) power) = ((prime ^ power : ℕ) : ℝ≥0∞) := by
  let unit := padicPrimePowerUnit (prime := prime) power
  have preimage : (ContinuousAddEquiv.mulLeft unit) ⁻¹' {value : ℚ_[prime] | ‖value‖ ≤ 1} =
      padicInversePowerBall power := by
    ext value
    change ‖unit.val * value‖ ≤ 1 ↔ ‖value‖ ≤ ‖unit.val‖⁻¹
    rw [norm_mul]
    simpa only [one_div, mul_comm] using
      (le_div_iff₀ (norm_pos_iff.mpr unit.ne_zero) : ‖value‖ ≤ 1 / ‖unit.val‖ ↔ ‖value‖ * ‖unit.val‖ ≤ 1).symm
  have scaling := addEquivAddHaarChar_smul_preimage measure
    (X := {value : ℚ_[prime] | ‖value‖ ≤ 1}) (ContinuousAddEquiv.mulLeft unit)
  rw [preimage, normalized] at scaling
  change (addEquivAddHaarChar (ContinuousAddEquiv.mulLeft unit) : ℝ≥0∞) *
    measure (padicInversePowerBall power) = 1 at scaling
  rw [padicHaarChar_primePower measure normalized power unit rfl] at scaling
  have equality := ENNReal.eq_inv_of_mul_eq_one_left ((mul_comm _ _).trans scaling)
  simpa only [inv_inv] using equality

end TernaryPeriodPolynomials.SphericalDetection.Helpers
