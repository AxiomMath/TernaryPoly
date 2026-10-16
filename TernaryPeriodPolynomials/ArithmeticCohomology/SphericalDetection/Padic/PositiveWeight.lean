module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Padic.NormPowerIntegrability

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def padicPositiveWeight {prime : ℕ} [Fact prime.Prime] (exponent : ℂ)
    (pair : ℚ_[prime] × ℚ_[prime]) : ℝ :=
  ‖padicNormPowerWeight exponent
    ‖(GeneralLinearGroup.det (padicPlanePivotCoordinates pair.1 pair.2).block).val‖‖

theorem padicPositiveWeight_nonneg {prime : ℕ} [Fact prime.Prime] (exponent : ℂ)
    (pair : ℚ_[prime] × ℚ_[prime]) : 0 ≤ padicPositiveWeight exponent pair := norm_nonneg _

theorem padicPositiveWeight_integrable {prime : ℕ} [Fact prime.Prime]
    [MeasurableSpace ℚ_[prime]] [BorelSpace ℚ_[prime]]
    (measure : Measure ℚ_[prime]) [measure.IsAddHaarMeasure]
    (normalized : measure {value : ℚ_[prime] | ‖value‖ ≤ 1} = 1)
    (exponent : ℂ) (convergent : 2 < exponent.re) :
    Integrable (padicPositiveWeight (prime := prime) exponent) (measure.prod measure) := by
  have integrable := padicNormPowerWeight_integrable measure normalized exponent convergent
    (fun _ => 1) (fun _ _ => rfl) ⟨1, fun _ => by simp⟩
  change Integrable (fun pair : ℚ_[prime] × ℚ_[prime] =>
    ‖padicNormPowerWeight exponent
      ‖(GeneralLinearGroup.det (padicPlanePivotCoordinates pair.1 pair.2).block).val‖‖) _
  simpa only [padicPlaneWeightedValue, mul_one] using integrable.norm

theorem padicPositiveWeight_square {prime : ℕ} [Fact prime.Prime] (exponent : ℂ)
    (pair : ℚ_[prime] × ℚ_[prime]) (member : pair ∈ padicPlaneIntegrationRegion 0) :
    padicPositiveWeight exponent pair = 1 := by
  rw [padicPositiveWeight, padicPlaneIntegrationRegion_det_norm 0 pair member,
    pow_zero, inv_one, padicNormPowerWeight_one, norm_one]

theorem padicPositiveWeight_integral_le {prime : ℕ} [Fact prime.Prime]
    [MeasurableSpace ℚ_[prime]] [BorelSpace ℚ_[prime]]
    (measure : Measure ℚ_[prime]) [measure.IsAddHaarMeasure]
    (normalized : measure {value : ℚ_[prime] | ‖value‖ ≤ 1} = 1)
    (exponent : ℂ) (convergent : 2 < exponent.re) :
    (∫ pair, padicPositiveWeight (prime := prime) exponent pair ∂(measure.prod measure)) ≤
      (1 - Real.exp ((2 - exponent.re) * Real.log prime))⁻¹ := by
  have integrable := padicPositiveWeight_integrable measure normalized exponent convergent
  have partition := hasSum_integral_iUnion (padicPlaneIntegrationRegion_measurable (prime := prime))
    padicPlaneIntegrationRegion_disjoint (show IntegrableOn (padicPositiveWeight exponent)
      (⋃ power, padicPlaneIntegrationRegion power) (measure.prod measure) from integrable.integrableOn)
  rw [padicPlaneIntegrationRegion_union, setIntegral_univ] at partition
  have bound (power : ℕ) :
      (∫ pair in padicPlaneIntegrationRegion power, padicPositiveWeight (prime := prime) exponent pair
        ∂(measure.prod measure)) ≤ (Real.exp ((2 - exponent.re) * Real.log prime)) ^ power := by
    have estimate := padicPlaneIntegrationRegion_integral_norm_le measure normalized
      (padicNormPowerWeight exponent) (fun _ => 1) (fun _ _ => rfl) 1 (fun _ => by simp) power
    simpa only [padicPositiveWeight, padicPlaneWeightedValue, mul_one, one_mul,
      padicNormPowerWeight_geometric prime (Nat.Prime.pos Fact.out) exponent] using estimate
  have small : ‖Real.exp ((2 - exponent.re) * Real.log prime)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_lt_one_iff]
    exact mul_neg_of_neg_of_pos (by linarith)
      (Real.log_pos (by exact_mod_cast Nat.Prime.one_lt (p := prime) Fact.out))
  have geometric := hasSum_geometric_of_norm_lt_one small
  exact hasSum_le bound partition geometric

end TernaryPeriodPolynomials.SphericalDetection.Helpers
