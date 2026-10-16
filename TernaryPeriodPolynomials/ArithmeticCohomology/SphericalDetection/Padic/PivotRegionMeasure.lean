module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Padic.PivotShellMeasure

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open scoped ENNReal

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def padicPivotRegion {prime : ℕ} [Fact prime.Prime] (power : ℕ)
    (index : Fin (prime ^ power)) : Set (ℚ_[prime] × ℚ_[prime]) :=
  {pair | pair.1 ∈ padicPivotShell power ∧ ‖pair.2 + (index.val : ℚ_[prime]) * pair.1‖ ≤ 1}

theorem padicPivotRegion_measurable {prime : ℕ} [Fact prime.Prime]
    [MeasurableSpace ℚ_[prime]] [BorelSpace ℚ_[prime]] (power : ℕ) (index : Fin (prime ^ power)) :
    MeasurableSet (padicPivotRegion power index) :=
  ((padicPivotShell_measurable power).preimage measurable_fst).inter
    ((isClosed_le (continuous_snd.add (continuous_const.mul continuous_fst)).norm
      continuous_const).measurableSet)

theorem padicPivotRegion_measure_shell {prime : ℕ} [Fact prime.Prime]
    [MeasurableSpace ℚ_[prime]] [BorelSpace ℚ_[prime]]
    (measure : Measure ℚ_[prime]) [measure.IsAddHaarMeasure]
    (normalized : measure {value : ℚ_[prime] | ‖value‖ ≤ 1} = 1)
    (power : ℕ) (index : Fin (prime ^ power)) :
    (measure.prod measure) (padicPivotRegion power index) = measure (padicPivotShell (prime := prime) power) := by
  rw [Measure.prod_apply (padicPivotRegion_measurable power index)]
  have fibers (pivot : ℚ_[prime]) :
      measure (Prod.mk pivot ⁻¹' padicPivotRegion power index) =
        (padicPivotShell (prime := prime) power).indicator (1 : ℚ_[prime] → ℝ≥0∞) pivot := by
    by_cases member : pivot ∈ padicPivotShell power
    · rw [Set.indicator_of_mem member]
      have preimage : Prod.mk pivot ⁻¹' padicPivotRegion power index =
          (fun other : ℚ_[prime] => other + (index.val : ℚ_[prime]) * pivot) ⁻¹'
            {value : ℚ_[prime] | ‖value‖ ≤ 1} := by
        ext other
        exact and_iff_right member
      rw [preimage, measure_preimage_add_right, normalized]
      rfl
    · rw [Set.indicator_of_notMem member]
      have preimage : Prod.mk pivot ⁻¹' padicPivotRegion power index = ∅ := by
        ext other
        simp only [Set.mem_preimage, padicPivotRegion, Set.mem_ofPred_eq, member, false_and, Set.mem_empty_iff_false]
      rw [preimage, measure_empty]
  simp_rw [fibers]
  exact lintegral_indicator_one (padicPivotShell_measurable power)

theorem padicPivotRegion_measure {prime : ℕ} [Fact prime.Prime]
    [MeasurableSpace ℚ_[prime]] [BorelSpace ℚ_[prime]]
    (measure : Measure ℚ_[prime]) [measure.IsAddHaarMeasure]
    (normalized : measure {value : ℚ_[prime] | ‖value‖ ≤ 1} = 1)
    (power : ℕ) (index : Fin (prime ^ (power + 1))) :
    (measure.prod measure) (padicPivotRegion (power + 1) index) =
      ((prime ^ (power + 1) : ℕ) : ℝ≥0∞) - ((prime ^ power : ℕ) : ℝ≥0∞) := by
  rw [padicPivotRegion_measure_shell measure normalized, padicPivotShell_measure measure normalized]

theorem padicPivotRegion_swap_measure {prime : ℕ} [Fact prime.Prime]
    [MeasurableSpace ℚ_[prime]] [BorelSpace ℚ_[prime]]
    (measure : Measure ℚ_[prime]) [measure.IsAddHaarMeasure]
    (normalized : measure {value : ℚ_[prime] | ‖value‖ ≤ 1} = 1)
    (power : ℕ) (index : Fin (prime ^ (power + 1))) :
    (measure.prod measure) (Prod.swap ⁻¹' padicPivotRegion (power + 1) index) =
      ((prime ^ (power + 1) : ℕ) : ℝ≥0∞) - ((prime ^ power : ℕ) : ℝ≥0∞) := by
  rw [← Measure.map_apply measurable_swap (padicPivotRegion_measurable (power + 1) index),
    Measure.prod_swap, padicPivotRegion_measure measure normalized]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
