module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Padic.PivotRegionValues

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open scoped ENNReal

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def padicPlaneWeightedValue {prime : ℕ} [Fact prime.Prime]
    (weight : ℝ → ℂ) (value : GeneralLinearGroup (Fin 2) ℚ_[prime] → ℂ) (pair : ℚ_[prime] × ℚ_[prime]) : ℂ :=
  weight ‖(GeneralLinearGroup.det (padicPlanePivotCoordinates pair.1 pair.2).block).val‖ *
    value (padicPlanePivotCoordinates pair.1 pair.2).block

theorem padicPlaneWeightedValue_first_region {prime : ℕ} [Fact prime.Prime]
    (weight : ℝ → ℂ) (value : GeneralLinearGroup (Fin 2) ℚ_[prime] → ℂ)
    (fixed : ∀ matrix compact, value (matrix * GeneralLinearGroup.map PadicInt.Coe.ringHom compact) = value matrix)
    (power : ℕ) (positive : 0 < power) (index : Fin (prime ^ power))
    (pair : ℚ_[prime] × ℚ_[prime]) (member : pair ∈ padicPivotRegion power index) :
    padicPlaneWeightedValue weight value pair =
      weight ((prime : ℝ) ^ power)⁻¹ * value (padicUpperPrimitiveRepresentative power index) := by
  have union_mem : pair ∈ ⋃ index : Fin (prime ^ power), padicPivotRegion power index :=
    Set.mem_iUnion.mpr ⟨index, member⟩
  rw [padicPivotRegion_union] at union_mem
  have pivot_norm : ‖pair.1‖ = (prime : ℝ) ^ power := member.1
  rw [padicPlaneWeightedValue, padicPlanePivotValue_first_region value fixed power positive index pair member,
    padicPlanePivotCoordinates_det_norm, max_eq_left union_mem.2,
    max_eq_right (padicPivotShell_large positive member.1).le, pivot_norm]

theorem padicPlaneWeightedValue_second_region {prime : ℕ} [Fact prime.Prime]
    (weight : ℝ → ℂ) (value : GeneralLinearGroup (Fin 2) ℚ_[prime] → ℂ)
    (fixed : ∀ matrix compact, value (matrix * GeneralLinearGroup.map PadicInt.Coe.ringHom compact) = value matrix)
    (power : ℕ) (positive : 0 < power) (index : Fin (prime ^ power)) (divisible : prime ∣ index.val)
    (pair : ℚ_[prime] × ℚ_[prime]) (member : pair.swap ∈ padicPivotRegion power index) :
    padicPlaneWeightedValue weight value pair =
      weight ((prime : ℝ) ^ power)⁻¹ * value (padicLowerPrimitiveRepresentative power index) := by
  have dominant : ‖pair.1‖ < ‖pair.2‖ :=
    (padicPivotRegion_strict_iff power positive index pair.swap member).mpr divisible
  have pivot_norm : ‖pair.2‖ = (prime : ℝ) ^ power := member.1
  have large : 1 < ‖pair.2‖ := padicPivotShell_large positive member.1
  rw [padicPlaneWeightedValue, padicPlanePivotValue_second_region value fixed power positive index divisible pair member,
    padicPlanePivotCoordinates_det_norm, max_eq_right dominant.le,
    max_eq_right large.le, pivot_norm]

theorem padicPlaneWeightedValue_first_integral {prime : ℕ} [Fact prime.Prime]
    [MeasurableSpace ℚ_[prime]] [BorelSpace ℚ_[prime]]
    (measure : Measure ℚ_[prime]) [measure.IsAddHaarMeasure]
    (normalized : measure {x : ℚ_[prime] | ‖x‖ ≤ 1} = 1)
    (weight : ℝ → ℂ) (value : GeneralLinearGroup (Fin 2) ℚ_[prime] → ℂ)
    (fixed : ∀ matrix compact, value (matrix * GeneralLinearGroup.map PadicInt.Coe.ringHom compact) = value matrix)
    (power : ℕ) (index : Fin (prime ^ (power + 1))) :
    IntegrableOn (padicPlaneWeightedValue weight value) (padicPivotRegion (power + 1) index) (measure.prod measure) ∧
      (∫ pair in padicPivotRegion (power + 1) index, padicPlaneWeightedValue weight value pair ∂(measure.prod measure)) =
        ((((prime ^ (power + 1) : ℕ) : ℝ≥0∞) - ((prime ^ power : ℕ) : ℝ≥0∞)).toReal) •
          (weight ((prime : ℝ) ^ (power + 1))⁻¹ * value (padicUpperPrimitiveRepresentative (power + 1) index)) := by
  have finite : (measure.prod measure) (padicPivotRegion (power + 1) index) ≠ ⊤ := by
    rw [padicPivotRegion_measure measure normalized]
    exact ENNReal.sub_ne_top (ENNReal.natCast_ne_top _)
  have equality := padicPlaneWeightedValue_first_region weight value fixed (power + 1) (Nat.succ_pos _) index
  constructor
  · exact (integrableOn_const finite).congr_fun (fun pair member => (equality pair member).symm)
      (padicPivotRegion_measurable (power + 1) index)
  · rw [setIntegral_congr_fun (padicPivotRegion_measurable (power + 1) index) equality, setIntegral_const]
    rw [Measure.real, padicPivotRegion_measure measure normalized]

theorem padicPlaneWeightedValue_second_integral {prime : ℕ} [Fact prime.Prime]
    [MeasurableSpace ℚ_[prime]] [BorelSpace ℚ_[prime]]
    (measure : Measure ℚ_[prime]) [measure.IsAddHaarMeasure]
    (normalized : measure {x : ℚ_[prime] | ‖x‖ ≤ 1} = 1)
    (weight : ℝ → ℂ) (value : GeneralLinearGroup (Fin 2) ℚ_[prime] → ℂ)
    (fixed : ∀ matrix compact, value (matrix * GeneralLinearGroup.map PadicInt.Coe.ringHom compact) = value matrix)
    (power : ℕ) (index : Fin (prime ^ (power + 1))) (divisible : prime ∣ index.val) :
    IntegrableOn (padicPlaneWeightedValue weight value) (Prod.swap ⁻¹' padicPivotRegion (power + 1) index)
        (measure.prod measure) ∧
      (∫ pair in Prod.swap ⁻¹' padicPivotRegion (power + 1) index,
        padicPlaneWeightedValue weight value pair ∂(measure.prod measure)) =
        ((((prime ^ (power + 1) : ℕ) : ℝ≥0∞) - ((prime ^ power : ℕ) : ℝ≥0∞)).toReal) •
          (weight ((prime : ℝ) ^ (power + 1))⁻¹ * value (padicLowerPrimitiveRepresentative (power + 1) index)) := by
  have measurable := (padicPivotRegion_measurable (power + 1) index).preimage measurable_swap
  have finite : (measure.prod measure) (Prod.swap ⁻¹' padicPivotRegion (power + 1) index) ≠ ⊤ := by
    rw [padicPivotRegion_swap_measure measure normalized]
    exact ENNReal.sub_ne_top (ENNReal.natCast_ne_top _)
  have equality := padicPlaneWeightedValue_second_region weight value fixed (power + 1) (Nat.succ_pos _) index divisible
  constructor
  · exact (integrableOn_const finite).congr_fun (fun pair member => (equality pair member).symm) measurable
  · rw [setIntegral_congr_fun measurable equality, setIntegral_const]
    rw [Measure.real, padicPivotRegion_swap_measure measure normalized]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
