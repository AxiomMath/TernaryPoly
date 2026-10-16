module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.SqrtTwoApproximation
public import Mathlib.Analysis.PSeries

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RotationCircle TernaryPeriodPolynomials.PlaneEisensteinContinuation.FourierDifferentiation
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.SmallDivisorKernel TernaryPeriodPolynomials.PlaneEisensteinContinuation.RotationRealization

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.RotationKernel

theorem fourier_sub_norm (first second : ℤ) (parameter : Parameter) :
    ‖fourier first parameter - fourier second parameter‖ =
      ‖fourier (first - second) parameter - 1‖ := by
  calc
    _ = ‖(fourier first parameter - fourier second parameter) * fourier (-second) parameter‖ := by
      rw [norm_mul, fourier_norm_one, mul_one]
    _ = _ := by rw [sub_mul, fourier_mul_neg, sub_eq_add_neg first second, fourier_add]

theorem frequency_sub_norm (first second : ℤ) :
    ‖frequency first - frequency second‖ = (2 * Real.pi) * |((first - second : ℤ) : ℝ)| := by
  have equality : frequency first - frequency second =
      (2 * Real.pi * Complex.I) * ((first - second : ℤ) : ℂ) := by
    simp only [frequency, Int.cast_sub]
    ring
  rw [equality, norm_mul, norm_mul, norm_mul, Complex.norm_I, mul_one]
  rw [Complex.norm_intCast]
  simp only [Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos]

theorem inverseCoefficients_bound (bound : ℝ)
    (estimate : ∀ index : ℤ,
      ‖(fourier index (Real.sqrt 2 : Parameter) - 1)⁻¹‖ ≤ bound * |(index : ℝ)|)
    (target index : ℤ) :
    ‖inverseCoefficients target 3 (Real.sqrt 2 : Parameter) index‖ ≤
      (bound / (2 * Real.pi) ^ 3) * (1 / (((-index - target : ℤ) : ℝ) ^ 2)) := by
  let difference : ℤ := -index - target
  have fourierBound :
      ‖(fourier (-index) (Real.sqrt 2 : Parameter) - fourier target (Real.sqrt 2 : Parameter))⁻¹‖ ≤
        bound * |(difference : ℝ)| := by
    rw [norm_inv, fourier_sub_norm, ← norm_inv]
    exact estimate difference
  have normEquality : ‖inverseCoefficients target 3 (Real.sqrt 2 : Parameter) index‖ =
      ‖(fourier (-index) (Real.sqrt 2 : Parameter) - fourier target (Real.sqrt 2 : Parameter))⁻¹‖ *
        (((2 * Real.pi) * |(difference : ℝ)|) ^ 3)⁻¹ := by
    simp only [inverseCoefficients, norm_inv, norm_mul, norm_pow, mul_inv_rev,
      frequency_sub_norm, difference, mul_comm]
  rw [normEquality]
  calc
    _ ≤ (bound * |(difference : ℝ)|) * (((2 * Real.pi) * |(difference : ℝ)|) ^ 3)⁻¹ :=
      mul_le_mul_of_nonneg_right fourierBound (inv_nonneg.mpr (by positivity))
    _ = _ := by
      change bound * |(difference : ℝ)| * ((2 * Real.pi * |(difference : ℝ)|) ^ 3)⁻¹ =
        bound / (2 * Real.pi) ^ 3 * (1 / ((difference : ℝ) ^ 2))
      by_cases zeroDifference : difference = 0
      · simp [zeroDifference]
      · have nonzeroDifference : (difference : ℝ) ≠ 0 := by exact_mod_cast zeroDifference
        have nonzeroAbs : |(difference : ℝ)| ≠ 0 := abs_ne_zero.mpr nonzeroDifference
        field_simp
        rw [sq_abs]

/-- Three shifted rotation derivatives make the inverse difference multiplier absolutely summable. -/
theorem summable_inverseCoefficients (target : ℤ) :
    Summable (fun index : ℤ => ‖inverseCoefficients target 3 (Real.sqrt 2 : Parameter) index‖) := by
  obtain ⟨bound, _, estimate⟩ := TernaryPeriodPolynomials.PlaneEisensteinContinuation.SqrtTwoApproximation.exists_inverse_bound
  have series : Summable (fun index : ℤ => (1 : ℝ) / (index : ℝ) ^ 2) :=
    Real.summable_one_div_int_pow.mpr (by norm_num)
  have injective : Function.Injective (fun index : ℤ => -index - target) := by
    intro first second equality
    exact neg_injective (sub_left_injective equality)
  have shifted : Summable (fun index : ℤ => (1 : ℝ) / (((-index - target : ℤ) : ℝ) ^ 2)) :=
    series.comp_injective injective
  apply (shifted.mul_left (bound / (2 * Real.pi) ^ 3)).of_nonneg_of_le
  · intro index
    exact norm_nonneg _
  · intro index
    exact inverseCoefficients_bound bound estimate target index

/-- The supplied algebraic realization commutes with each actual Hilbert rotation projection. -/
theorem scalarCoefficient_eq_mode (data : CuspidalRepresentation) (point : BinaryAdelicGL)
    (target : ℤ) (vector : data.smooth) :
    scalarCoefficient data point target vector = data.realize (RotationFourier.smoothMode data target vector) point :=
  scalarCoefficient_eq_mode_of_summable_inverse data point target 3 (Real.sqrt 2) irrational_sqrt_two
    (summable_inverseCoefficients target) vector

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.RotationKernel
