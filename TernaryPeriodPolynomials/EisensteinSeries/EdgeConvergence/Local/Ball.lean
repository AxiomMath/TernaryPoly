module

public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.Local.Coordinates
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Padic.HaarNorm

@[expose] public section


/-!
# Haar measure of balls in `ℚ₃`

For the Haar measure of `ℚ₃` giving the ring of integers mass one, the closed ball of radius `3^k`
has mass `3^k`; consequently the closed ball of radius `M ≥ 1` has mass between `M / 3` and `3 M`.
-/

open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open scoped ENNReal NNReal

noncomputable section

namespace TernaryPeriodPolynomials.EdgeConvergence

local instance normalizedLocalThreeMeasure_isAddHaar' :
    normalizedLocalThreeMeasure.IsAddHaarMeasure :=
  normalizedLocalThreeMeasure_haar

/-- The closed ball of radius `3^k` in `ℚ₃` has mass `3^k`. -/
theorem localBall_measure_pow (k : ℕ) :
    normalizedLocalThreeMeasure {value : ℚ_[3] | ‖value‖ ≤ (3 : ℝ) ^ k} = 3 ^ k := by
  have nonzero : ((3 : ℕ) : ℚ_[3]) ^ k ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.mpr (by norm_num))
  let unit : ℚ_[3]ˣ := Units.mk0 (((3 : ℕ) : ℚ_[3]) ^ k) nonzero
  have ballEquality : {value : ℚ_[3] | ‖unit.val * value‖ ≤ 1} =
      {value : ℚ_[3] | ‖value‖ ≤ (3 : ℝ) ^ k} := by
    ext value
    simp only [Set.mem_ofPred_eq, unit, Units.val_mk0, norm_mul, norm_pow, Padic.norm_p]
    have positive : (0 : ℝ) < (3 : ℝ) ^ k := by positivity
    rw [show (((3 : ℕ) : ℝ)⁻¹) ^ k = ((3 : ℝ) ^ k)⁻¹ by simp, inv_mul_le_iff₀ positive, mul_one]
  have measureEquality := padicHaarChar_ball_measure normalizedLocalThreeMeasure
    normalizedLocalThreeMeasure_normalized unit
  rw [ballEquality] at measureEquality
  rw [measureEquality]
  have character : addEquivAddHaarChar (ContinuousAddEquiv.mulLeft unit) = ((3 : ℝ≥0)⁻¹) ^ k := by
    apply NNReal.coe_injective
    rw [padicHaarChar_eq_norm normalizedLocalThreeMeasure
      normalizedLocalThreeMeasure_normalized unit]
    have threeNorm : ‖(3 : ℚ_[3])‖ = 3⁻¹ := by simpa using Padic.norm_p (p := 3)
    simp [unit, threeNorm]
  rw [character]
  simp [ENNReal.coe_inv, ENNReal.inv_pow]

/-- The closed ball of radius `M ≥ 1` in `ℚ₃` has mass between `M / 3` and `3 M`. -/
theorem localBall_real_bounds (radius : ℝ) (large : 1 ≤ radius) :
    radius / 3 ≤ normalizedLocalThreeMeasure.real {value : ℚ_[3] | ‖value‖ ≤ radius} ∧
      normalizedLocalThreeMeasure.real {value : ℚ_[3] | ‖value‖ ≤ radius} ≤ 3 * radius := by
  obtain ⟨k, lower, upper⟩ := exists_nat_pow_near large (by norm_num : (1 : ℝ) < 3)
  have upperFinite : normalizedLocalThreeMeasure {value : ℚ_[3] | ‖value‖ ≤ (3 : ℝ) ^ (k + 1)} =
      3 ^ (k + 1) := localBall_measure_pow (k + 1)
  have lowerSubset : {value : ℚ_[3] | ‖value‖ ≤ (3 : ℝ) ^ k} ⊆ {value : ℚ_[3] | ‖value‖ ≤ radius} :=
    fun value membership => membership.trans lower
  have upperSubset : {value : ℚ_[3] | ‖value‖ ≤ radius} ⊆
      {value : ℚ_[3] | ‖value‖ ≤ (3 : ℝ) ^ (k + 1)} :=
    fun value membership => membership.trans upper.le
  have finiteUpper : normalizedLocalThreeMeasure {value : ℚ_[3] | ‖value‖ ≤ (3 : ℝ) ^ (k + 1)} ≠ ⊤ := by
    rw [upperFinite]
    exact ENNReal.pow_ne_top (by norm_num)
  have finiteRadius : normalizedLocalThreeMeasure {value : ℚ_[3] | ‖value‖ ≤ radius} ≠ ⊤ :=
    ne_top_of_le_ne_top finiteUpper (measure_mono upperSubset)
  constructor
  · have mono := ENNReal.toReal_mono finiteRadius (measure_mono lowerSubset)
    rw [localBall_measure_pow] at mono
    have cast : ((3 : ℝ≥0∞) ^ k).toReal = (3 : ℝ) ^ k := by
      rw [ENNReal.toReal_pow]
      norm_num
    change _ ≤ (normalizedLocalThreeMeasure _).toReal
    rw [cast] at mono
    rw [pow_succ] at upper
    linarith
  · have mono := ENNReal.toReal_mono finiteUpper (measure_mono upperSubset)
    rw [upperFinite] at mono
    have cast : ((3 : ℝ≥0∞) ^ (k + 1)).toReal = (3 : ℝ) ^ (k + 1) := by
      rw [ENNReal.toReal_pow]
      norm_num
    change (normalizedLocalThreeMeasure _).toReal ≤ _
    rw [cast] at mono
    rw [pow_succ] at mono
    linarith

end TernaryPeriodPolynomials.EdgeConvergence
