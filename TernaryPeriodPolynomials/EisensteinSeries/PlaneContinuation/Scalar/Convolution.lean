module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Scalar.FourierOperator
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

@[expose] public section


open MeasureTheory TernaryPeriodPolynomials.PlaneEisensteinContinuation.RotationCircle TernaryPeriodPolynomials.PlaneEisensteinContinuation.ScalarFourierOperator

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.ScalarConvolution

noncomputable def translate (function : C(Parameter, ℂ)) (parameter : Parameter) : C(Parameter, ℂ) :=
  ⟨fun point => function (parameter + point), function.continuous.comp (continuous_const.add continuous_id)⟩

theorem translate_continuous (function : C(Parameter, ℂ)) : Continuous (translate function) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact function.continuous.comp (continuous_fst.add continuous_snd)

theorem weighted_translate_integrable (kernel function : C(Parameter, ℂ)) :
    Integrable (fun parameter => kernel parameter • translate function parameter) AddCircle.haarAddCircle :=
  (kernel.continuous.smul (translate_continuous function)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

noncomputable def convolution (kernel function : C(Parameter, ℂ)) : C(Parameter, ℂ) :=
  ∫ parameter : Parameter, kernel parameter • translate function parameter ∂AddCircle.haarAddCircle

theorem convolution_apply (kernel function : C(Parameter, ℂ)) (point : Parameter) :
    convolution kernel function point =
      ∫ parameter : Parameter, kernel parameter * function (parameter + point) ∂AddCircle.haarAddCircle :=
  ContinuousMap.integral_apply (weighted_translate_integrable kernel function) point

theorem convolution_fourierCoeff (kernel function : C(Parameter, ℂ)) (index : ℤ) :
    fourierCoeff (convolution kernel function) index =
      fourierCoeff kernel (-index) * fourierCoeff function index := by
  change coefficientOperator index
    (∫ parameter : Parameter, kernel parameter • translate function parameter ∂AddCircle.haarAddCircle) = _
  rw [← (coefficientOperator index).integral_comp_comm (weighted_translate_integrable kernel function)]
  calc
    _ = ∫ parameter : Parameter,
        (fourier index parameter * kernel parameter) * fourierCoeff function index ∂AddCircle.haarAddCircle := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun parameter => by
        change coefficientOperator index (kernel parameter • translate function parameter) =
          (fourier index parameter * kernel parameter) * fourierCoeff function index
        rw [map_smul, coefficientOperator_apply]
        change kernel parameter * fourierCoeff (fun point => function (parameter + point)) index = _
        rw [fourierCoeff_translate]
        ring)
    _ = _ := by
      rw [integral_mul_const]
      unfold fourierCoeff
      simp only [neg_neg, smul_eq_mul]

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.ScalarConvolution
