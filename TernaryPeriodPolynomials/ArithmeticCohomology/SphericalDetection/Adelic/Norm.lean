module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory
open scoped ENNReal NNReal

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem adeleNorm_realAdeleUnit (unit : ℝˣ) :
    (adeleNorm (realAdeleUnit unit) : ℝ) = |unit.val| := by
  let lattice : Set FiniteAdeles := Set.range integralEmbedding
  let box : Set Adeles := Set.Icc (-|unit.val|) |unit.val| ×ˢ lattice
  have positive : 0 < |unit.val| := abs_pos.mpr unit.ne_zero
  have preimage :
      (ContinuousAddEquiv.mulLeft (realAdeleUnit unit)) ⁻¹' box =
        Set.Icc (-1) 1 ×ˢ lattice := by
    ext point
    change (-|unit.val| ≤ unit.val * point.1 ∧ unit.val * point.1 ≤ |unit.val|) ∧
        1 * point.2 ∈ lattice ↔ (-1 ≤ point.1 ∧ point.1 ≤ 1) ∧ point.2 ∈ lattice
    rw [one_mul, ← abs_le, abs_mul, ← abs_le]
    have bound : |unit.val| * |point.1| ≤ |unit.val| ↔ |point.1| ≤ 1 := by
      simpa only [mul_one] using
        (mul_le_mul_iff_right₀ positive :
          |unit.val| * |point.1| ≤ |unit.val| * 1 ↔ |point.1| ≤ 1)
    rw [bound]
  have unit_volume : adeleMeasure (Set.Icc (-1) 1 ×ˢ lattice) = 2 := by
    rw [adeleMeasure, Measure.prod_prod, finiteMeasure_integralLattice]
    norm_num
  have box_volume : adeleMeasure box = ENNReal.ofReal (2 * |unit.val|) := by
    rw [adeleMeasure, Measure.prod_prod, finiteMeasure_integralLattice]
    simp only [Real.volume_Icc, sub_neg_eq_add, mul_one, two_mul]
  have scale := addEquivAddHaarChar_smul_preimage adeleMeasure
    (X := box) (ContinuousAddEquiv.mulLeft (realAdeleUnit unit))
  rw [preimage, unit_volume, box_volume] at scale
  change (adeleNorm (realAdeleUnit unit) : ℝ≥0∞) * 2 = ENNReal.ofReal (2 * |unit.val|) at scale
  have real_scale := congrArg ENNReal.toReal scale
  simp only [ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.toReal_ofNat,
    ENNReal.toReal_ofReal (show 0 ≤ 2 * |unit.val| from
      mul_nonneg (by norm_num) positive.le)] at real_scale
  linarith

theorem adeleNorm_realAdeleUnit_of_pos (unit : ℝˣ) (positive : 0 < unit.val) :
    (adeleNorm (realAdeleUnit unit) : ℝ) = unit.val := by
  let lattice : Set FiniteAdeles := Set.range integralEmbedding
  let box : Set Adeles := Set.Icc 0 unit.val ×ˢ lattice
  have preimage :
      (ContinuousAddEquiv.mulLeft (realAdeleUnit unit)) ⁻¹' box =
        Set.Icc 0 1 ×ˢ lattice := by
    ext point
    change (0 ≤ unit.val * point.1 ∧ unit.val * point.1 ≤ unit.val) ∧
        1 * point.2 ∈ lattice ↔ (0 ≤ point.1 ∧ point.1 ≤ 1) ∧ point.2 ∈ lattice
    have upper : unit.val * point.1 ≤ unit.val ↔ point.1 ≤ 1 := by
      simpa only [mul_one] using
        (show unit.val * point.1 ≤ unit.val * 1 ↔ point.1 ≤ 1 from
          mul_le_mul_iff_right₀ positive)
    rw [one_mul, mul_nonneg_iff_of_pos_left positive, upper]
  have unit_volume : adeleMeasure (Set.Icc 0 1 ×ˢ lattice) = 1 := by
    rw [adeleMeasure, Measure.prod_prod, finiteMeasure_integralLattice]
    norm_num
  have box_volume : adeleMeasure box = ENNReal.ofReal unit.val := by
    rw [adeleMeasure, Measure.prod_prod, finiteMeasure_integralLattice]
    simp only [Real.volume_Icc, sub_zero, mul_one]
  have scale := addEquivAddHaarChar_smul_preimage adeleMeasure
    (X := box) (ContinuousAddEquiv.mulLeft (realAdeleUnit unit))
  rw [preimage, unit_volume, box_volume] at scale
  change (adeleNorm (realAdeleUnit unit) : ℝ≥0∞) * 1 = ENNReal.ofReal unit.val at scale
  rw [mul_one] at scale
  have real_scale := congrArg ENNReal.toReal scale
  simpa only [ENNReal.coe_toReal, ENNReal.toReal_ofReal positive.le] using real_scale

theorem normPower_realAdeleUnit_of_pos (unit : ℝˣ) (positive : 0 < unit.val)
    (exponent : ℂ) :
    normPower (realAdeleUnit unit) exponent = (unit.val : ℂ) ^ exponent := by
  rw [normPower, adeleNorm_realAdeleUnit_of_pos unit positive,
    Complex.ofReal_log positive.le,
    Complex.cpow_def_of_ne_zero (by exact_mod_cast unit.ne_zero)]
  congr 1
  exact mul_comm _ _

end TernaryPeriodPolynomials.SphericalDetection.Helpers
