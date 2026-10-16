module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Padic.HaarScaling

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open scoped ENNReal

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem padicInversePowerBall_norm {prime : ℕ} [Fact prime.Prime] (power : ℕ) :
    padicInversePowerBall (prime := prime) power = {value : ℚ_[prime] | ‖value‖ ≤ (prime : ℝ) ^ power} := by
  ext value
  change ‖value‖ ≤ ‖(prime : ℚ_[prime]) ^ power‖⁻¹ ↔ ‖value‖ ≤ (prime : ℝ) ^ power
  rw [Padic.norm_p_pow, zpow_neg, inv_inv, zpow_natCast]

def padicPivotShell {prime : ℕ} [Fact prime.Prime] (power : ℕ) : Set ℚ_[prime] :=
  {value | ‖value‖ = (prime : ℝ) ^ power}

theorem padicPivotShell_measurable {prime : ℕ} [Fact prime.Prime]
    [MeasurableSpace ℚ_[prime]] [BorelSpace ℚ_[prime]] (power : ℕ) :
    MeasurableSet (padicPivotShell (prime := prime) power) :=
  (isClosed_eq continuous_norm continuous_const).measurableSet

theorem padicPivotShell_eq_diff {prime : ℕ} [Fact prime.Prime] (power : ℕ) :
    padicPivotShell (prime := prime) (power + 1) =
      padicInversePowerBall (power + 1) \ padicInversePowerBall power := by
  rw [padicInversePowerBall_norm, padicInversePowerBall_norm]
  ext value
  have discrete : ‖value‖ ≤ (prime : ℝ) ^ power ↔ ‖value‖ < (prime : ℝ) ^ (power + 1) := by
    simpa only [← Int.natCast_add_one, zpow_natCast] using
      Padic.norm_le_pow_iff_norm_lt_pow_add_one value (power : ℤ)
  change ‖value‖ = (prime : ℝ) ^ (power + 1) ↔
    ‖value‖ ≤ (prime : ℝ) ^ (power + 1) ∧ ¬‖value‖ ≤ (prime : ℝ) ^ power
  rw [discrete, not_lt]
  exact le_antisymm_iff

theorem padicInversePowerBall_subset {prime : ℕ} [Fact prime.Prime] (power : ℕ) :
    padicInversePowerBall (prime := prime) power ⊆ padicInversePowerBall (power + 1) := by
  rw [padicInversePowerBall_norm, padicInversePowerBall_norm]
  intro value member
  change ‖value‖ ≤ (prime : ℝ) ^ power at member
  change ‖value‖ ≤ (prime : ℝ) ^ (power + 1)
  exact member.trans (pow_le_pow_right₀ (by exact_mod_cast (Nat.Prime.one_lt (Fact.out : prime.Prime)).le)
    (Nat.le_succ power))

theorem padicPivotShell_measure {prime : ℕ} [Fact prime.Prime]
    [MeasurableSpace ℚ_[prime]] [BorelSpace ℚ_[prime]]
    (measure : Measure ℚ_[prime]) [measure.IsAddHaarMeasure]
    (normalized : measure {value : ℚ_[prime] | ‖value‖ ≤ 1} = 1) (power : ℕ) :
    measure (padicPivotShell (prime := prime) (power + 1)) =
      ((prime ^ (power + 1) : ℕ) : ℝ≥0∞) - ((prime ^ power : ℕ) : ℝ≥0∞) := by
  rw [padicPivotShell_eq_diff, measure_sdiff (padicInversePowerBall_subset power)
    (padicInversePowerBall_measurable power).nullMeasurableSet]
  · rw [padicInversePowerBall_measure measure normalized, padicInversePowerBall_measure measure normalized]
  · rw [padicInversePowerBall_measure measure normalized]
    exact ENNReal.natCast_ne_top _

end TernaryPeriodPolynomials.SphericalDetection.Helpers
