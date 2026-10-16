module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Padic.LatticeMeasure

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def padicPivotFiber {prime : ℕ} [Fact prime.Prime] (power : ℕ) (pivot : ℚ_[prime]ˣ)
    (index : Fin (prime ^ power)) : Set ℚ_[prime] :=
  (fun other => -other * pivot.inv) ⁻¹' padicResidueClass power index

theorem padicPivotFiber_translate {prime : ℕ} [Fact prime.Prime] (power : ℕ) (pivot : ℚ_[prime]ˣ)
    (index : Fin (prime ^ power)) (shell : ‖pivot.val⁻¹‖ = ‖(prime : ℚ_[prime]) ^ power‖) :
    padicPivotFiber power pivot index =
      (fun other => other + (index.val : ℚ_[prime]) * pivot.val) ⁻¹' {value : ℚ_[prime] | ‖value‖ ≤ 1} := by
  ext other
  change ‖-other * pivot.inv - (index.val : ℚ_[prime])‖ ≤ ‖(prime : ℚ_[prime]) ^ power‖ ↔ _
  have algebra : -other * pivot.inv - (index.val : ℚ_[prime]) =
      -(other + (index.val : ℚ_[prime]) * pivot.val) / pivot.val := by
    change -other * (pivot⁻¹).val - _ = _
    rw [Units.val_inv_eq_inv_val]
    field_simp
    ring
  rw [algebra, ← shell, norm_div, norm_neg, norm_inv]
  change ‖other + (index.val : ℚ_[prime]) * pivot.val‖ / ‖pivot.val‖ ≤ ‖pivot.val‖⁻¹ ↔
    ‖other + (index.val : ℚ_[prime]) * pivot.val‖ ≤ 1
  rw [div_le_iff₀ (norm_pos_iff.mpr pivot.ne_zero), inv_mul_cancel₀ (norm_ne_zero_iff.mpr pivot.ne_zero)]

theorem padicPivotFiber_measurable {prime : ℕ} [Fact prime.Prime]
    [MeasurableSpace ℚ_[prime]] [BorelSpace ℚ_[prime]]
    (power : ℕ) (pivot : ℚ_[prime]ˣ) (index : Fin (prime ^ power)) :
    MeasurableSet (padicPivotFiber power pivot index) :=
  (padicResidueClass_measurable power index).preimage
    (continuous_id.neg.mul continuous_const).measurable

theorem padicPivotFiber_measure {prime : ℕ} [Fact prime.Prime]
    [MeasurableSpace ℚ_[prime]] [BorelSpace ℚ_[prime]]
    (measure : Measure ℚ_[prime]) [measure.IsAddHaarMeasure]
    (normalized : measure {value : ℚ_[prime] | ‖value‖ ≤ 1} = 1)
    (power : ℕ) (pivot : ℚ_[prime]ˣ) (index : Fin (prime ^ power))
    (shell : ‖pivot.val⁻¹‖ = ‖(prime : ℚ_[prime]) ^ power‖) :
    measure (padicPivotFiber power pivot index) = 1 := by
  rw [padicPivotFiber_translate power pivot index shell, measure_preimage_add_right, normalized]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
