module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Padic.PrimitiveShellPartition

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open scoped ENNReal

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def padicPrimitiveSum {prime : ℕ} [Fact prime.Prime] (power : ℕ)
    (value : GeneralLinearGroup (Fin 2) ℚ_[prime] → ℂ) : ℂ := by
  classical
  exact ∑ index : Fin (prime ^ power) ⊕ {index : Fin (prime ^ power) // prime ∣ index.val},
    value (padicPrimitiveRepresentative power index)

theorem padicPrimitiveRegion_integral {prime : ℕ} [Fact prime.Prime]
    [MeasurableSpace ℚ_[prime]] [BorelSpace ℚ_[prime]]
    (measure : Measure ℚ_[prime]) [measure.IsAddHaarMeasure]
    (normalized : measure {x : ℚ_[prime] | ‖x‖ ≤ 1} = 1)
    (weight : ℝ → ℂ) (value : GeneralLinearGroup (Fin 2) ℚ_[prime] → ℂ)
    (fixed : ∀ matrix compact, value (matrix * GeneralLinearGroup.map PadicInt.Coe.ringHom compact) = value matrix)
    (power : ℕ) (index : Fin (prime ^ (power + 1)) ⊕ {index : Fin (prime ^ (power + 1)) // prime ∣ index.val}) :
    IntegrableOn (padicPlaneWeightedValue weight value) (padicPrimitiveRegion (power + 1) index) (measure.prod measure) ∧
      (∫ pair in padicPrimitiveRegion (power + 1) index,
        padicPlaneWeightedValue weight value pair ∂(measure.prod measure)) =
        ((((prime ^ (power + 1) : ℕ) : ℝ≥0∞) - ((prime ^ power : ℕ) : ℝ≥0∞)).toReal) •
          (weight ((prime : ℝ) ^ (power + 1))⁻¹ * value (padicPrimitiveRepresentative (power + 1) index)) := by
  cases index with
  | inl index => exact padicPlaneWeightedValue_first_integral measure normalized weight value fixed power index
  | inr index => exact padicPlaneWeightedValue_second_integral measure normalized weight value fixed power index.val index.property

/-- The local two-variable shell integral is its exact primitive triangular sum times the common fiber measure. -/
theorem padicPrimitiveShell_integral {prime : ℕ} [Fact prime.Prime]
    [MeasurableSpace ℚ_[prime]] [BorelSpace ℚ_[prime]]
    (measure : Measure ℚ_[prime]) [measure.IsAddHaarMeasure]
    (normalized : measure {x : ℚ_[prime] | ‖x‖ ≤ 1} = 1)
    (weight : ℝ → ℂ) (value : GeneralLinearGroup (Fin 2) ℚ_[prime] → ℂ)
    (fixed : ∀ matrix compact, value (matrix * GeneralLinearGroup.map PadicInt.Coe.ringHom compact) = value matrix)
    (power : ℕ) :
    IntegrableOn (padicPlaneWeightedValue weight value)
        {pair : ℚ_[prime] × ℚ_[prime] | max ‖pair.1‖ ‖pair.2‖ = (prime : ℝ) ^ (power + 1)} (measure.prod measure) ∧
      (∫ pair in {pair : ℚ_[prime] × ℚ_[prime] | max ‖pair.1‖ ‖pair.2‖ = (prime : ℝ) ^ (power + 1)},
        padicPlaneWeightedValue weight value pair ∂(measure.prod measure)) =
        ((((prime ^ (power + 1) : ℕ) : ℝ≥0∞) - ((prime ^ power : ℕ) : ℝ≥0∞)).toReal) •
          (weight ((prime : ℝ) ^ (power + 1))⁻¹ * padicPrimitiveSum (power + 1) value) := by
  classical
  have pieces := padicPrimitiveRegion_integral measure normalized weight value fixed power
  rw [← padicPrimitiveRegion_union (power + 1) (Nat.succ_pos _)]
  constructor
  · exact integrableOn_finite_iUnion.mpr (fun index => (pieces index).1)
  · rw [integral_iUnion_fintype (padicPrimitiveRegion_measurable (power + 1))
      (padicPrimitiveRegion_disjoint (power + 1) (Nat.succ_pos _)) (fun index => (pieces index).1)]
    simp_rw [fun index => (pieces index).2]
    rw [← Finset.smul_sum, ← Finset.mul_sum]
    rfl

theorem padicPlaneWeightedValue_integral_square {prime : ℕ} [Fact prime.Prime]
    [MeasurableSpace ℚ_[prime]] [BorelSpace ℚ_[prime]]
    (measure : Measure ℚ_[prime]) [measure.IsAddHaarMeasure]
    (normalized : measure {x : ℚ_[prime] | ‖x‖ ≤ 1} = 1)
    (weight : ℝ → ℂ) (value : GeneralLinearGroup (Fin 2) ℚ_[prime] → ℂ) :
    IntegrableOn (padicPlaneWeightedValue weight value)
        {pair : ℚ_[prime] × ℚ_[prime] | ‖pair.1‖ ≤ 1 ∧ ‖pair.2‖ ≤ 1} (measure.prod measure) ∧
      (∫ pair in {pair : ℚ_[prime] × ℚ_[prime] | ‖pair.1‖ ≤ 1 ∧ ‖pair.2‖ ≤ 1},
        padicPlaneWeightedValue weight value pair ∂(measure.prod measure)) = weight 1 * value 1 := by
  have measurable : MeasurableSet {pair : ℚ_[prime] × ℚ_[prime] | ‖pair.1‖ ≤ 1 ∧ ‖pair.2‖ ≤ 1} :=
    ((isClosed_le continuous_fst.norm continuous_const).inter
      (isClosed_le continuous_snd.norm continuous_const)).measurableSet
  have volume : (measure.prod measure) {pair : ℚ_[prime] × ℚ_[prime] | ‖pair.1‖ ≤ 1 ∧ ‖pair.2‖ ≤ 1} = 1 := by
    change (measure.prod measure) ({x : ℚ_[prime] | ‖x‖ ≤ 1} ×ˢ {x : ℚ_[prime] | ‖x‖ ≤ 1}) = 1
    rw [Measure.prod_prod, normalized, one_mul]
  have equality : Set.EqOn (padicPlaneWeightedValue weight value) (fun _ => weight 1 * value 1)
      {pair : ℚ_[prime] × ℚ_[prime] | ‖pair.1‖ ≤ 1 ∧ ‖pair.2‖ ≤ 1} := by
    intro pair member
    rw [padicPlaneWeightedValue, padicPlanePivotCoordinates_integral pair.1 pair.2 member.1 member.2,
      map_one, Units.val_one, norm_one]
  constructor
  · exact (integrableOn_const (volume.trans_ne ENNReal.one_ne_top)).congr_fun
      (fun pair member => (equality member).symm) measurable
  · rw [setIntegral_congr_fun measurable equality, setIntegral_const, Measure.real, volume, ENNReal.toReal_one, one_smul]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
