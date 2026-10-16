module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Scalar.FourierOperator

@[expose] public section


open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RotationCircle TernaryPeriodPolynomials.PlaneEisensteinContinuation.ScalarFourierOperator

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.FourierSeriesKernel

theorem fourier_norm_le (index : ℤ) : ‖(fourier index : C(Parameter, ℂ))‖ ≤ 1 := by
  apply (ContinuousMap.norm_le _ (by norm_num)).mpr
  intro point
  exact (fourier_norm_one index point).le

theorem summable_series (coefficients : ℤ → ℂ) (summability : Summable (fun index => ‖coefficients index‖)) :
    Summable (fun index : ℤ => coefficients index • (fourier index : C(Parameter, ℂ))) := by
  apply summability.of_norm_bounded
  intro index
  rw [norm_smul]
  exact (mul_le_mul_of_nonneg_left (fourier_norm_le index) (norm_nonneg _)).trans_eq (mul_one _)

noncomputable def kernel (coefficients : ℤ → ℂ) : C(Parameter, ℂ) :=
  ∑' index : ℤ, coefficients index • fourier index

theorem kernel_fourierCoeff (coefficients : ℤ → ℂ) (summability : Summable (fun index => ‖coefficients index‖))
    (index : ℤ) : fourierCoeff (kernel coefficients) index = coefficients index := by
  change coefficientOperator index (∑' frequencyIndex : ℤ, coefficients frequencyIndex • fourier frequencyIndex) = _
  rw [(coefficientOperator index).map_tsum (summable_series coefficients summability)]
  have termEquality : (fun frequencyIndex : ℤ => coefficientOperator index
      (coefficients frequencyIndex • fourier frequencyIndex)) =
      (fun frequencyIndex : ℤ => if frequencyIndex = index then coefficients index else 0) := by
    funext frequencyIndex
    rw [map_smul, coefficientOperator_apply, fourierCoeff_fourier]
    by_cases same : frequencyIndex = index
    · subst frequencyIndex
      simp
    · simp [same, Ne.symm same]
  rw [termEquality]
  exact (hasSum_ite_eq index (coefficients index)).tsum_eq

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.FourierSeriesKernel
