module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Adelic.ThetaDistortion
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

@[expose] public section


open MeasureTheory TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.RealFourierLinear

def dual (transform : RealSpace ≃L[ℝ] RealSpace) : RealSpace ≃L[ℝ] RealSpace :=
  ContinuousLinearEquiv.equivOfInverse' (ContinuousLinearMap.adjoint transform.symm.toContinuousLinearMap)
    (ContinuousLinearMap.adjoint transform.toContinuousLinearMap)
    (by
      rw [← ContinuousLinearMap.adjoint_comp]
      have equality : transform.toContinuousLinearMap.comp transform.symm.toContinuousLinearMap =
          ContinuousLinearMap.id ℝ RealSpace := by ext vector; simp
      rw [equality, ContinuousLinearMap.adjoint_id])
    (by
      rw [← ContinuousLinearMap.adjoint_comp]
      have equality : transform.symm.toContinuousLinearMap.comp transform.toContinuousLinearMap =
          ContinuousLinearMap.id ℝ RealSpace := by ext vector; simp
      rw [equality, ContinuousLinearMap.adjoint_id])

def factor (transform : RealSpace ≃L[ℝ] RealSpace) : ℝ :=
  |(LinearMap.det transform.toLinearEquiv.toLinearMap)⁻¹|

theorem factor_positive (transform : RealSpace ≃L[ℝ] RealSpace) : 0 < factor transform :=
  abs_pos.mpr (inv_ne_zero transform.toLinearEquiv.isUnit_det'.ne_zero)

theorem dual_apply (transform : RealSpace ≃L[ℝ] RealSpace) (value : RealSpace) :
    dual transform value = ContinuousLinearMap.adjoint transform.symm.toContinuousLinearMap value := rfl

theorem dual_inverse_norm (transform : RealSpace ≃L[ℝ] RealSpace) :
    ‖(dual transform).symm.toContinuousLinearMap‖ = ‖transform.toContinuousLinearMap‖ :=
  ContinuousLinearMap.adjoint.norm_map transform.toContinuousLinearMap

theorem transformed_inner (transform : RealSpace ≃L[ℝ] RealSpace) (value frequency : RealSpace) :
    inner ℝ (transform value) (dual transform frequency) = inner ℝ value frequency := by
  rw [dual_apply, ContinuousLinearMap.adjoint_inner_right]
  simp only [ContinuousLinearEquiv.coe_coe, transform.symm_apply_apply]

theorem integral_comp (transform : RealSpace ≃L[ℝ] RealSpace) (function : RealSpace → ℂ) :
    (∫ value, function (transform value)) = factor transform • ∫ value, function value := by
  have mapMeasure : Measure.map transform volume = ENNReal.ofReal (factor transform) • volume :=
    Measure.map_linearMap_addHaar_eq_smul_addHaar volume transform.toLinearEquiv.isUnit_det'.ne_zero
  have equality := transform.toHomeomorph.toMeasurableEquiv.measurableEmbedding.integral_map (μ := volume) function
  change (∫ value, function value ∂Measure.map transform volume) = ∫ value, function (transform value) at equality
  rw [mapMeasure, integral_smul_measure, ENNReal.toReal_ofReal (factor_positive transform).le] at equality
  exact equality.symm

theorem fourier_pullback (function : SchwartzMap RealSpace ℂ) (transform : RealSpace ≃L[ℝ] RealSpace)
    (frequency : RealSpace) :
    FourierTransform.fourier (AdelicThetaDistortion.pullback function transform) frequency =
      factor transform • FourierTransform.fourier function (dual transform frequency) := by
  rw [RealFourierScaling.fourier_integral, RealFourierScaling.fourier_integral]
  have equality := integral_comp transform
    (fun value => (Real.fourierChar (-inner ℝ value (dual transform frequency)) : ℂ) * function value)
  rw [← equality]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro value
  dsimp only
  rw [transformed_inner, AdelicThetaDistortion.pullback_apply]

theorem fourier_pullback_eq (function : SchwartzMap RealSpace ℂ) (transform : RealSpace ≃L[ℝ] RealSpace) :
    FourierTransform.fourier (AdelicThetaDistortion.pullback function transform) =
      factor transform • AdelicThetaDistortion.pullback (FourierTransform.fourier function) (dual transform) := by
  ext frequency
  exact fourier_pullback function transform frequency

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.RealFourierLinear
