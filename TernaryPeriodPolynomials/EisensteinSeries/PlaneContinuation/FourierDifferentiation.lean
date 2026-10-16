module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.FourierUniqueness
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

@[expose] public section


open MeasureTheory TernaryPeriodPolynomials.PlaneEisensteinContinuation.RotationCircle

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.FourierDifferentiation

noncomputable def frequency (index : ℤ) : ℂ := 2 * Real.pi * Complex.I * index

theorem frequency_neg (index : ℤ) : frequency (-index) = -frequency index := by
  simp [frequency]

theorem fourier_hasDerivAt (index : ℤ) (time : ℝ) :
    HasDerivAt (fun point : ℝ => fourier index (point : Parameter))
      (frequency index * fourier index (time : Parameter)) time := by
  have linearDerivative : HasDerivAt (fun point : ℝ => frequency index * (point : ℂ)) (frequency index) time := by
    convert (hasDerivAt_id time).ofReal_comp.const_mul (frequency index) using 1 <;>
      first | rfl | simp only [Complex.ofReal_one, mul_one]
  have exponentialDerivative := linearDerivative.cexp
  have formula (point : ℝ) : fourier index (point : Parameter) = Complex.exp (frequency index * (point : ℂ)) := by
    simp only [fourier_coe_apply, Complex.ofReal_one, div_one, frequency]
  have curveEquality : (fun point : ℝ => fourier index (point : Parameter)) =
      (fun point : ℝ => Complex.exp (frequency index * (point : ℂ))) := funext formula
  rw [curveEquality, formula, mul_comm]
  exact exponentialDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
theorem fourierCoeff_eq_integral (function : Parameter → E) (index : ℤ) :
    fourierCoeff function index =
      ∫ point : ℝ in 0..1, fourier (-index) (point : Parameter) • function (point : Parameter) := by
  simpa only [div_one, one_smul, zero_add] using fourierCoeff_eq_intervalIntegral function index 0

/-- Differentiating a periodic vector-valued curve multiplies its Fourier coefficient by its frequency. -/
theorem fourierCoeff_derivative (function derivative : Parameter → E) (continuousDerivative : Continuous derivative)
    (hasDerivative : ∀ time : ℝ, HasDerivAt (fun point : ℝ => function (point : Parameter))
      (derivative (time : Parameter)) time) (index : ℤ) :
    fourierCoeff derivative index = frequency index • fourierCoeff function index := by
  let : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ ℂ E
  have continuousQuotient : Continuous (fun time : ℝ => (time : Parameter)) := continuous_quot_mk
  have weightIntegrable : IntervalIntegrable
      (fun time : ℝ => frequency (-index) * fourier (-index) (time : Parameter)) volume 0 1 :=
    (continuous_const.mul ((fourier (-index)).continuous.comp continuousQuotient)).intervalIntegrable _ _
  have derivativeIntegrable : IntervalIntegrable (fun time : ℝ => derivative (time : Parameter)) volume 0 1 :=
    (continuousDerivative.comp continuousQuotient).intervalIntegrable _ _
  have parts := intervalIntegral.integral_smul_deriv_eq_deriv_smul
    (fun time (_ : time ∈ Set.uIcc (0 : ℝ) 1) => fourier_hasDerivAt (-index) time)
    (fun time (_ : time ∈ Set.uIcc (0 : ℝ) 1) => hasDerivative time) weightIntegrable derivativeIntegrable
  rw [fourierCoeff_eq_integral, fourierCoeff_eq_integral]
  calc
    _ = fourier (-index) ((1 : ℝ) : Parameter) • function ((1 : ℝ) : Parameter) -
        fourier (-index) ((0 : ℝ) : Parameter) • function ((0 : ℝ) : Parameter) -
        ∫ point : ℝ in 0..1, (frequency (-index) * fourier (-index) (point : Parameter)) •
          function (point : Parameter) := parts
    _ = _ := by
      simp only [AddCircle.coe_period, AddCircle.coe_zero, sub_self, zero_sub, mul_smul,
        frequency_neg, neg_smul]
      rw [intervalIntegral.integral_neg, neg_neg]
      exact intervalIntegral.integral_smul _ _

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.FourierDifferentiation
