module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Rotation.Realization
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.FourierSeriesKernel
public import Mathlib.NumberTheory.Real.Irrational

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RotationCircle TernaryPeriodPolynomials.PlaneEisensteinContinuation.FourierDifferentiation TernaryPeriodPolynomials.PlaneEisensteinContinuation.RotationRealization

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.SmallDivisorKernel

theorem frequency_injective : Function.Injective frequency := by
  intro first second equality
  have nonzero : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
  have castEquality : (first : ℂ) = second := mul_left_cancel₀ nonzero equality
  exact_mod_cast castEquality

theorem fourier_injective_of_irrational (angle : ℝ) (irrationality : Irrational angle) :
    Function.Injective (fun index : ℤ => fourier index (angle : Parameter)) := by
  intro first second equality
  by_contra different
  have circleEquality : AddCircle.toCircle (first • (angle : Parameter)) = AddCircle.toCircle (second • (angle : Parameter)) :=
    Subtype.ext equality
  have parameterEquality := AddCircle.injective_toCircle (T := (1 : ℝ)) one_ne_zero circleEquality
  have quotientZero : (((first - second) • angle : ℝ) : Parameter) = 0 := by
    rw [AddCircle.coe_zsmul, sub_zsmul, parameterEquality]
    exact add_neg_cancel _
  obtain ⟨integer, integerEquality⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp quotientZero
  have irrationalProduct := irrationality.intCast_mul (sub_ne_zero.mpr different)
  apply irrationalProduct.ne_int integer
  simpa only [zsmul_eq_mul, mul_one] using integerEquality.symm

/-- Fourier coefficients of a candidate inverse to one rotation difference after taking shifted derivatives. -/
noncomputable def inverseCoefficients (target : ℤ) (order : ℕ) (parameter : Parameter) (index : ℤ) : ℂ :=
  ((fourier (-index) parameter - fourier target parameter) *
    (frequency (-index) - frequency target) ^ order)⁻¹

theorem kernel_multiplier (target : ℤ) (order : ℕ) (parameter : Parameter)
    (nonresonance : Function.Injective (fun index : ℤ => fourier index parameter))
    (summability : Summable (fun index : ℤ => ‖inverseCoefficients target order parameter index‖))
    (index : ℤ) (different : index ≠ target) :
    (fourier index parameter - fourier target parameter) *
        fourierCoeff (FourierSeriesKernel.kernel (inverseCoefficients target order parameter)) (-index) *
      (frequency index - frequency target) ^ order = 1 := by
  rw [FourierSeriesKernel.kernel_fourierCoeff _ summability]
  unfold inverseCoefficients
  rw [neg_neg]
  have firstNonzero : fourier index parameter - fourier target parameter ≠ 0 :=
    sub_ne_zero.mpr (fun equality => different (nonresonance equality))
  have secondNonzero : frequency index - frequency target ≠ 0 :=
    sub_ne_zero.mpr (fun equality => different (frequency_injective equality))
  calc
    _ = ((fourier index parameter - fourier target parameter) * (frequency index - frequency target) ^ order) *
        ((fourier index parameter - fourier target parameter) * (frequency index - frequency target) ^ order)⁻¹ := by ring
    _ = 1 := mul_inv_cancel₀ (mul_ne_zero firstNonzero (pow_ne_zero order secondNonzero))

theorem scalarCoefficient_eq_mode_of_summable_inverse (data : CuspidalRepresentation) (point : BinaryAdelicGL)
    (target : ℤ) (order : ℕ) (angle : ℝ) (irrationality : Irrational angle)
    (summability : Summable (fun index : ℤ => ‖inverseCoefficients target order (angle : Parameter) index‖))
    (vector : data.smooth) :
    scalarCoefficient data point target vector = data.realize (RotationFourier.smoothMode data target vector) point :=
  scalarCoefficient_eq_mode_of_multiplier data point target order
    (FourierSeriesKernel.kernel (inverseCoefficients target order (angle : Parameter))) (angle : Parameter)
    (kernel_multiplier target order (angle : Parameter) (fourier_injective_of_irrational angle irrationality) summability) vector

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.SmallDivisorKernel
