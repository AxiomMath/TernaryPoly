module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Scalar.RotationCoefficients

@[expose] public section


open MeasureTheory

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

theorem circleFourierCoefficient_norm_le (weight : ℤ) (function : C(AddCircle (1 : ℝ), ℂ)) :
    ‖fourierCoeff function weight‖ ≤ ‖function‖ := by
  change ‖∫ angle, fourier (-weight) angle * function angle ∂AddCircle.haarAddCircle‖ ≤ _
  calc
    _ ≤ ∫ angle, ‖fourier (-weight) angle * function angle‖ ∂AddCircle.haarAddCircle := norm_integral_le_integral_norm _
    _ ≤ ∫ _ : AddCircle (1 : ℝ), ‖function‖ ∂AddCircle.haarAddCircle := by
      apply integral_mono (circle_fourier_integrable function weight).norm (integrable_const _)
      intro angle
      dsimp only
      rw [norm_mul, circle_fourier_norm, one_mul]
      exact function.norm_coe_le_norm angle
    _ = _ := by simp

noncomputable def circleFourierCoefficientContinuous (weight : ℤ) : C(AddCircle (1 : ℝ), ℂ) →L[ℂ] ℂ :=
  (circleFourierCoefficientLinear weight).mkContinuous 1
    (fun function => by
      change ‖fourierCoeff function weight‖ ≤ 1 * ‖function‖
      simpa only [one_mul] using circleFourierCoefficient_norm_le weight function)

theorem continuousFourierSeries_summable (coefficients : ℤ → ℂ)
    (summable : Summable (fun weight => ‖coefficients weight‖)) :
    Summable (fun weight : ℤ => coefficients weight • (fourier weight : C(AddCircle (1 : ℝ), ℂ))) := by
  apply Summable.of_norm
  simpa only [norm_smul, fourier_norm, mul_one] using summable

noncomputable def continuousFourierSeries (coefficients : ℤ → ℂ) : C(AddCircle (1 : ℝ), ℂ) :=
  ∑' weight : ℤ, coefficients weight • fourier weight

theorem continuousFourierSeries_coefficient (coefficients : ℤ → ℂ)
    (summable : Summable (fun weight => ‖coefficients weight‖)) (weight : ℤ) :
    fourierCoeff (continuousFourierSeries coefficients) weight = coefficients weight := by
  classical
  change circleFourierCoefficientContinuous weight
    (∑' index : ℤ, coefficients index • (fourier index : C(AddCircle (1 : ℝ), ℂ))) = _
  rw [(circleFourierCoefficientContinuous weight).map_tsum (continuousFourierSeries_summable coefficients summable)]
  have term (index : ℤ) :
      circleFourierCoefficientContinuous weight (coefficients index • fourier index) =
        if index = weight then coefficients index else 0 := by
    rw [map_smul]
    change coefficients index • fourierCoeff (fourier index) weight = _
    rw [fourierCoeff_fourier]
    simp [Pi.single_apply, eq_comm]
  simp only [term, tsum_ite_eq]

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
