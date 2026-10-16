module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Padic.PlaneRegionBounds

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open scoped ENNReal

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem padicPlaneIntegrationRegion_integral_norm_le {prime : ℕ} [Fact prime.Prime]
    [MeasurableSpace ℚ_[prime]] [BorelSpace ℚ_[prime]]
    (measure : Measure ℚ_[prime]) [measure.IsAddHaarMeasure]
    (normalized : measure {value : ℚ_[prime] | ‖value‖ ≤ 1} = 1)
    (weight : ℝ → ℂ) (value : GeneralLinearGroup (Fin 2) ℚ_[prime] → ℂ)
    (fixed : ∀ matrix compact, value (matrix * GeneralLinearGroup.map PadicInt.Coe.ringHom compact) = value matrix)
    (bound : ℝ) (bounded : ∀ matrix, ‖value matrix‖ ≤ bound) (power : ℕ) :
    (∫ pair in padicPlaneIntegrationRegion power, ‖padicPlaneWeightedValue weight value pair‖ ∂(measure.prod measure)) ≤
      bound * (((prime : ℝ) ^ power) * ((prime : ℝ) ^ power) * ‖weight ((prime : ℝ) ^ power)⁻¹‖) := by
  have nonnegative : 0 ≤ bound := (norm_nonneg (value 1)).trans (bounded 1)
  have region_integrable := padicPlaneIntegrationRegion_integrable measure normalized weight value fixed power
  have constant_integrable : IntegrableOn (fun _ : ℚ_[prime] × ℚ_[prime] =>
      ‖weight ((prime : ℝ) ^ power)⁻¹‖ * bound) (padicPlaneIntegrationRegion power) (measure.prod measure) :=
    integrableOn_const (padicPlaneIntegrationRegion_measure_ne_top measure normalized power)
  have estimate := setIntegral_mono_on region_integrable.norm constant_integrable
    (padicPlaneIntegrationRegion_measurable power) (fun pair member => by
      rw [padicPlaneWeightedValue, norm_mul, padicPlaneIntegrationRegion_det_norm power pair member]
      exact mul_le_mul_of_nonneg_left (bounded _) (norm_nonneg _))
  rw [setIntegral_const, smul_eq_mul] at estimate
  have volume := ENNReal.toReal_mono
    (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.natCast_ne_top _))
    (padicPlaneIntegrationRegion_measure_le measure normalized power)
  simp only [ENNReal.toReal_mul, Nat.cast_pow] at volume
  calc
    _ ≤ (measure.prod measure).real (padicPlaneIntegrationRegion power) *
        (‖weight ((prime : ℝ) ^ power)⁻¹‖ * bound) := estimate
    _ ≤ ((prime : ℝ) ^ power * (prime : ℝ) ^ power) *
        (‖weight ((prime : ℝ) ^ power)⁻¹‖ * bound) :=
      mul_le_mul_of_nonneg_right volume (mul_nonneg (norm_nonneg _) nonnegative)
    _ = _ := by ring

theorem padicPlaneWeightedValue_integrable_of_summable {prime : ℕ} [Fact prime.Prime]
    [MeasurableSpace ℚ_[prime]] [BorelSpace ℚ_[prime]]
    (measure : Measure ℚ_[prime]) [measure.IsAddHaarMeasure]
    (normalized : measure {value : ℚ_[prime] | ‖value‖ ≤ 1} = 1)
    (weight : ℝ → ℂ) (value : GeneralLinearGroup (Fin 2) ℚ_[prime] → ℂ)
    (fixed : ∀ matrix compact, value (matrix * GeneralLinearGroup.map PadicInt.Coe.ringHom compact) = value matrix)
    (bounded : ∃ bound : ℝ, ∀ matrix, ‖value matrix‖ ≤ bound)
    (summable : Summable (fun power : ℕ =>
      ((prime : ℝ) ^ power) * ((prime : ℝ) ^ power) * ‖weight ((prime : ℝ) ^ power)⁻¹‖)) :
    Integrable (padicPlaneWeightedValue weight value) (measure.prod measure) := by
  obtain ⟨bound, bounded⟩ := bounded
  have sum_norm : Summable (fun power : ℕ => ∫ pair in padicPlaneIntegrationRegion power,
      ‖padicPlaneWeightedValue weight value pair‖ ∂(measure.prod measure)) :=
    Summable.of_nonneg_of_le (fun _ => integral_nonneg (fun _ => norm_nonneg _))
      (padicPlaneIntegrationRegion_integral_norm_le measure normalized weight value fixed bound bounded)
      (summable.mul_left bound)
  have integrable := integrableOn_iUnion_of_summable_integral_norm
    (padicPlaneIntegrationRegion_integrable measure normalized weight value fixed) sum_norm
  simpa only [padicPlaneIntegrationRegion_union, integrableOn_univ] using integrable

end TernaryPeriodPolynomials.SphericalDetection.Helpers
