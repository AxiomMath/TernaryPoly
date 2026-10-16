module

public import TernaryPeriodPolynomials.Analysis.Compact.SignedConvolutionSquare

@[expose] public section


/-! Actual fixed-kernel derivative L2 bounds without differentiating the input. -/
noncomputable section
namespace TernaryPoly.CompactCoordinateIntegration
open MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

theorem fderiv_scalarConvolution_eq_kernel (κ f : E → ℝ)
    (hκ : ContDiff ℝ 1 κ) (hcκ : HasCompactSupport κ)
    (hf : Continuous f) (hcf : HasCompactSupport f) (v : E) :
    (fun x => fderiv ℝ (scalarConvolution μ κ f) x v) =
      scalarConvolution μ (fun y => fderiv ℝ κ y v) f := by
  funext x
  exact fderiv_scalarConvolution μ κ f hκ hcκ hf hcf x v

theorem scalarConvolution_derivative_square_le (κ f : E → ℝ)
    (hκ : ContDiff ℝ 1 κ) (hcκ : HasCompactSupport κ)
    (hf : Continuous f) (hcf : HasCompactSupport f) (v : E) :
    ∫ x, ‖fderiv ℝ (scalarConvolution μ κ f) x v‖ ^ 2 ∂μ ≤
      (∫ z, ‖fderiv ℝ κ z v‖ ∂μ)^2 * ∫ y, ‖f y‖ ^ 2 ∂μ := by
  have hd : Continuous (fun y => fderiv ℝ κ y v) :=
    (hκ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have h := scalarConvolution_signed_square_le μ (fun y => fderiv ℝ κ y v) f
    (contDiff_zero.mpr hd) (hcκ.fderiv_apply ℝ v) hf hcf
  simpa only [← fderiv_scalarConvolution_eq_kernel μ κ f hκ hcκ hf hcf v] using h

end TernaryPoly.CompactCoordinateIntegration
