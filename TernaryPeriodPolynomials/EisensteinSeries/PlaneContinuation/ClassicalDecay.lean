module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.RightHalfPlane
public import Mathlib.NumberTheory.ModularForms.QExpansion

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.ClassicalCuspForms TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteClassicalComponents
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.ArithmeticModularity TernaryPeriodPolynomials.PlaneEisensteinContinuation.HighestWeightHolomorphic TernaryPeriodPolynomials.PlaneEisensteinContinuation.UpperTriangularChart
open Filter Asymptotics

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.ClassicalDecay

theorem period_three : (3 : ℝ) ∈ arithmeticGroup.strictPeriods := by
  rw [arithmeticGroup, CongruenceSubgroup.strictPeriods_Gamma]
  exact AddSubgroup.mem_zmultiples 3

theorem exponential {degree : ℕ} (data : InducingData degree) (point : IntegralBinaryGL)
    (vector : FiniteRotationTypes.fixedMode data.cusp finiteCongruence (-(degree + 3 : ℤ))) :
    (fun argument : UpperHalfPlane => realizationLinear data point vector argument) =O[UpperHalfPlane.atImInfty]
      (fun argument => Real.exp (-2 * Real.pi * argument.im / 3)) :=
  CuspFormClass.exp_decay_atImInfty (realizationLinear data point vector) (by norm_num) period_three

theorem uniform_exponential {degree : ℕ} (data : InducingData degree)
    (vector : FiniteRotationTypes.fixedMode data.cusp finiteCongruence (-(degree + 3 : ℤ))) :
    ∃ bound : ℝ, ∀ᶠ argument : UpperHalfPlane in UpperHalfPlane.atImInfty, ∀ point : IntegralBinaryGL,
      ‖realizationLinear data point vector argument‖ ≤ bound * Real.exp (-2 * Real.pi * argument.im / 3) := by
  classical
  let _ : Fintype Residue := Fintype.ofFinite _
  have familyBound : (fun argument : UpperHalfPlane => fun residue : Residue =>
      realizationLinear data (representative residue) vector argument) =O[UpperHalfPlane.atImInfty]
      (fun argument => Real.exp (-2 * Real.pi * argument.im / 3)) :=
    isBigO_pi.mpr (fun residue => exponential data (representative residue) vector)
  obtain ⟨bound, eventual⟩ := familyBound.isBigOWith
  refine ⟨bound, ?_⟩
  filter_upwards [eventual.bound] with argument boundProperty
  intro point
  let residue : Residue := ⟨GeneralLinearGroup.map integralReduction point, point, rfl⟩
  have equality : realizationLinear data (representative residue) = realizationLinear data point :=
    realizationLinear_equal_reduction data _ point (representative_reduction residue)
  have pointBound := (norm_le_pi_norm (fun residue : Residue =>
    realizationLinear data (representative residue) vector argument) residue).trans boundProperty
  simpa only [equality, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using pointBound

theorem raw_norm (data : CuspidalRepresentation) (point : BinaryAdelicGL) (vector : data.smooth)
    (weight : ℤ) (argument : UpperHalfPlane) :
    ‖raw data point vector argument‖ = argument.im ^ ((weight : ℝ) / 2) * ‖function data point vector weight argument‖ := by
  rw [function, norm_mul, HolomorphicDecay.normalization_norm weight argument argument.im_pos, ← mul_assoc]
  change ‖raw data point vector argument‖ =
    (argument.im ^ ((weight : ℝ) / 2) * argument.im ^ (-(weight : ℝ) / 2)) * ‖raw data point vector argument‖
  have powerProduct : argument.im ^ ((weight : ℝ) / 2) * argument.im ^ (-(weight : ℝ) / 2) = 1 := by
    rw [← Real.rpow_add argument.im_pos, show (weight : ℝ) / 2 + -(weight : ℝ) / 2 = 0 by ring, Real.rpow_zero]
  rw [powerProduct, one_mul]

theorem uniform_raw_exponential {degree : ℕ} (data : InducingData degree)
    (vector : FiniteRotationTypes.fixedMode data.cusp finiteCongruence (-(degree + 3 : ℤ))) :
    ∃ bound : ℝ, ∀ᶠ argument : UpperHalfPlane in UpperHalfPlane.atImInfty, ∀ point : IntegralBinaryGL,
      ‖data.cusp.realize vector.val (atFinite (GeneralLinearGroup.map integralEmbedding point) *
        atInfinity (unit argument argument.im_pos))‖ ≤
          argument.im ^ (((degree : ℝ) + 3) / 2) *
            (bound * Real.exp (-2 * Real.pi * argument.im / 3)) := by
  obtain ⟨bound, eventual⟩ := uniform_exponential data vector
  refine ⟨bound, ?_⟩
  filter_upwards [eventual] with argument pointBound
  intro point
  rw [← raw_eq data.cusp _ vector.val argument argument.im_pos, raw_norm data.cusp _ vector.val (degree + 3)]
  have boundAtPoint := mul_le_mul_of_nonneg_left (pointBound point)
    (Real.rpow_nonneg argument.im_pos.le (((degree : ℝ) + 3) / 2))
  simpa only [realizationLinear_apply, Int.cast_add, Int.cast_natCast, Int.cast_ofNat] using boundAtPoint

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.ClassicalDecay
