module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Padic.PlaneShellCover

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open scoped ENNReal

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def padicPrimitiveSeriesTerm {prime : ℕ} [Fact prime.Prime]
    (weight : ℝ → ℂ) (value : GeneralLinearGroup (Fin 2) ℚ_[prime] → ℂ) (power : ℕ) : ℂ :=
  ((((prime ^ (power + 1) : ℕ) : ℝ≥0∞) - ((prime ^ power : ℕ) : ℝ≥0∞)).toReal) •
    (weight ((prime : ℝ) ^ (power + 1))⁻¹ * padicPrimitiveSum (power + 1) value)

def padicPlaneSeriesTerm {prime : ℕ} [Fact prime.Prime]
    (weight : ℝ → ℂ) (value : GeneralLinearGroup (Fin 2) ℚ_[prime] → ℂ) : ℕ → ℂ
  | 0 => weight 1 * value 1
  | power + 1 => padicPrimitiveSeriesTerm weight value power

theorem padicPlaneIntegral_hasSum {prime : ℕ} [Fact prime.Prime]
    [MeasurableSpace ℚ_[prime]] [BorelSpace ℚ_[prime]]
    (measure : Measure ℚ_[prime]) [measure.IsAddHaarMeasure]
    (normalized : measure {x : ℚ_[prime] | ‖x‖ ≤ 1} = 1)
    (weight : ℝ → ℂ) (value : GeneralLinearGroup (Fin 2) ℚ_[prime] → ℂ)
    (fixed : ∀ matrix compact, value (matrix * GeneralLinearGroup.map PadicInt.Coe.ringHom compact) = value matrix)
    (integrable : Integrable (padicPlaneWeightedValue weight value) (measure.prod measure)) :
    HasSum (padicPlaneSeriesTerm weight value)
      (∫ pair, padicPlaneWeightedValue weight value pair ∂(measure.prod measure)) := by
  have decomposition := hasSum_integral_iUnion (padicPlaneIntegrationRegion_measurable (prime := prime))
    (padicPlaneIntegrationRegion_disjoint (prime := prime)) integrable.integrableOn
  have values (power : ℕ) :
      (∫ pair in padicPlaneIntegrationRegion power, padicPlaneWeightedValue weight value pair ∂(measure.prod measure)) =
        padicPlaneSeriesTerm weight value power := by
    cases power with
    | zero => exact (padicPlaneWeightedValue_integral_square measure normalized weight value).2
    | succ power => exact (padicPrimitiveShell_integral measure normalized weight value fixed power).2
  simp_rw [values] at decomposition
  simpa only [padicPlaneIntegrationRegion_union, setIntegral_univ] using decomposition

/-- The countable local shell expansion follows from integrability of the actual weighted local function. -/
theorem padicPlaneIntegral_series {prime : ℕ} [Fact prime.Prime]
    [MeasurableSpace ℚ_[prime]] [BorelSpace ℚ_[prime]]
    (measure : Measure ℚ_[prime]) [measure.IsAddHaarMeasure]
    (normalized : measure {x : ℚ_[prime] | ‖x‖ ≤ 1} = 1)
    (weight : ℝ → ℂ) (value : GeneralLinearGroup (Fin 2) ℚ_[prime] → ℂ)
    (fixed : ∀ matrix compact, value (matrix * GeneralLinearGroup.map PadicInt.Coe.ringHom compact) = value matrix)
    (integrable : Integrable (padicPlaneWeightedValue weight value) (measure.prod measure)) :
    Summable (padicPrimitiveSeriesTerm weight value) ∧
      (∫ pair, padicPlaneWeightedValue weight value pair ∂(measure.prod measure)) =
        weight 1 * value 1 + ∑' power, padicPrimitiveSeriesTerm weight value power := by
  have series := padicPlaneIntegral_hasSum measure normalized weight value fixed integrable
  constructor
  · exact (summable_nat_add_iff 1).mpr series.summable
  · exact series.tsum_eq.symm.trans series.summable.tsum_eq_zero_add

end TernaryPeriodPolynomials.SphericalDetection.Helpers
