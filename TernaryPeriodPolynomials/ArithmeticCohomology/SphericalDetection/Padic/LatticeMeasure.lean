module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Padic.ResidueLattice

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open scoped ENNReal

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem padicResidueClass_measure {prime : ℕ} [Fact prime.Prime]
    [MeasurableSpace ℚ_[prime]] [BorelSpace ℚ_[prime]]
    (measure : Measure ℚ_[prime]) [measure.IsAddHaarMeasure]
    (power : ℕ) (index : Fin (prime ^ power)) :
    measure (padicResidueClass power index) = measure (padicPrimePowerLattice (prime := prime) power) := by
  simpa only [padicResidueClass, sub_eq_add_neg] using
    measure_preimage_add_right measure (-(index.val : ℚ_[prime])) (padicPrimePowerLattice power)

theorem padicPrimePowerLattice_measure {prime : ℕ} [Fact prime.Prime]
    [MeasurableSpace ℚ_[prime]] [BorelSpace ℚ_[prime]]
    (measure : Measure ℚ_[prime]) [measure.IsAddHaarMeasure]
    (normalized : measure {value : ℚ_[prime] | ‖value‖ ≤ 1} = 1) (power : ℕ) :
    measure (padicPrimePowerLattice (prime := prime) power) = ((prime ^ power : ℕ) : ℝ≥0∞)⁻¹ := by
  have partition := measure_iUnion (μ := measure) (padicResidueClass_disjoint (prime := prime) power)
    (padicResidueClass_measurable power)
  rw [padicResidueClass_union, normalized] at partition
  simp only [padicResidueClass_measure, tsum_fintype, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at partition
  exact ENNReal.eq_inv_of_mul_eq_one_left ((mul_comm _ _).trans partition.symm)

theorem padicResidueClass_measure_normalized {prime : ℕ} [Fact prime.Prime]
    [MeasurableSpace ℚ_[prime]] [BorelSpace ℚ_[prime]]
    (measure : Measure ℚ_[prime]) [measure.IsAddHaarMeasure]
    (normalized : measure {value : ℚ_[prime] | ‖value‖ ≤ 1} = 1)
    (power : ℕ) (index : Fin (prime ^ power)) :
    measure (padicResidueClass power index) = ((prime ^ power : ℕ) : ℝ≥0∞)⁻¹ := by
  rw [padicResidueClass_measure, padicPrimePowerLattice_measure measure normalized]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
