module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Padic.PlaneIntegralSeries

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open scoped ENNReal

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem padicPlaneIntegrationRegion_det_norm {prime : ℕ} [Fact prime.Prime]
    (power : ℕ) (pair : ℚ_[prime] × ℚ_[prime]) (member : pair ∈ padicPlaneIntegrationRegion power) :
    ‖(GeneralLinearGroup.det (padicPlanePivotCoordinates pair.1 pair.2).block).val‖ =
      ((prime : ℝ) ^ power)⁻¹ := by
  rw [padicPlanePivotCoordinates_det_norm]
  cases power with
  | zero =>
      rw [max_eq_left (max_le member.1 member.2), pow_zero]
  | succ power =>
      change max ‖pair.1‖ ‖pair.2‖ = (prime : ℝ) ^ (power + 1) at member
      rw [member, max_eq_right]
      exact one_le_pow₀ (by exact_mod_cast (Nat.Prime.one_lt Fact.out).le)

theorem padicPlaneIntegrationRegion_measure_le {prime : ℕ} [Fact prime.Prime]
    [MeasurableSpace ℚ_[prime]] [BorelSpace ℚ_[prime]]
    (measure : Measure ℚ_[prime]) [measure.IsAddHaarMeasure]
    (normalized : measure {value : ℚ_[prime] | ‖value‖ ≤ 1} = 1) (power : ℕ) :
    (measure.prod measure) (padicPlaneIntegrationRegion (prime := prime) power) ≤
      ((prime ^ power : ℕ) : ℝ≥0∞) * ((prime ^ power : ℕ) : ℝ≥0∞) := by
  have ball : padicInversePowerBall (prime := prime) power = {value | ‖value‖ ≤ (prime : ℝ) ^ power} := by
    ext value
    simp only [padicInversePowerBall, Set.mem_ofPred_eq, norm_pow, Padic.norm_p, inv_pow, inv_inv]
  have subset : padicPlaneIntegrationRegion (prime := prime) power ⊆
      padicInversePowerBall power ×ˢ padicInversePowerBall power := by
    rw [ball]
    intro pair member
    cases power with
    | zero =>
        rw [pow_zero]
        exact member
    | succ power =>
        change max ‖pair.1‖ ‖pair.2‖ = (prime : ℝ) ^ (power + 1) at member
        exact ⟨(le_max_left _ _).trans member.le, (le_max_right _ _).trans member.le⟩
  have bound := measure_mono (μ := measure.prod measure) subset
  rwa [Measure.prod_prod, padicInversePowerBall_measure measure normalized] at bound

theorem padicPlaneIntegrationRegion_measure_ne_top {prime : ℕ} [Fact prime.Prime]
    [MeasurableSpace ℚ_[prime]] [BorelSpace ℚ_[prime]]
    (measure : Measure ℚ_[prime]) [measure.IsAddHaarMeasure]
    (normalized : measure {value : ℚ_[prime] | ‖value‖ ≤ 1} = 1) (power : ℕ) :
    (measure.prod measure) (padicPlaneIntegrationRegion (prime := prime) power) ≠ ⊤ :=
  ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.natCast_ne_top _))
    (padicPlaneIntegrationRegion_measure_le measure normalized power)

theorem padicPlaneIntegrationRegion_integrable {prime : ℕ} [Fact prime.Prime]
    [MeasurableSpace ℚ_[prime]] [BorelSpace ℚ_[prime]]
    (measure : Measure ℚ_[prime]) [measure.IsAddHaarMeasure]
    (normalized : measure {value : ℚ_[prime] | ‖value‖ ≤ 1} = 1)
    (weight : ℝ → ℂ) (value : GeneralLinearGroup (Fin 2) ℚ_[prime] → ℂ)
    (fixed : ∀ matrix compact, value (matrix * GeneralLinearGroup.map PadicInt.Coe.ringHom compact) = value matrix)
    (power : ℕ) :
    IntegrableOn (padicPlaneWeightedValue weight value) (padicPlaneIntegrationRegion power) (measure.prod measure) := by
  cases power with
  | zero => exact (padicPlaneWeightedValue_integral_square measure normalized weight value).1
  | succ power => exact (padicPrimitiveShell_integral measure normalized weight value fixed power).1

end TernaryPeriodPolynomials.SphericalDetection.Helpers
