module

public import TernaryPeriodPolynomials.Analysis.Compact.Coordinate.FormalAdjoint
public import Mathlib.Analysis.Convolution
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Analysis.Calculus.ContDiff.Convolution

@[expose] public section


/-! Scalar convolution and its actual derivative, for compact smooth local regularizers. -/
noncomputable section
namespace TernaryPoly.CompactCoordinateIntegration
open MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

/-- Scalar convolution with a compact smoothing kernel. -/
def scalarConvolution (κ f : E → ℝ) (x : E) : ℝ :=
  convolution f κ (ContinuousLinearMap.mul ℝ ℝ) μ x

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure] in
theorem scalarConvolution_apply (κ f : E → ℝ) (x : E) :
    scalarConvolution μ κ f x = ∫ y, f y * κ (x - y) ∂μ := rfl

/-- Actual differentiation of a compact smooth convolution kernel under the integral. -/
theorem fderiv_scalarConvolution (κ f : E → ℝ)
    (hκ : ContDiff ℝ 1 κ) (hcκ : HasCompactSupport κ)
    (hf : Continuous f) (hcf : HasCompactSupport f) (x v : E) :
    fderiv ℝ (scalarConvolution μ κ f) x v =
      ∫ y, f y * fderiv ℝ κ (x - y) v ∂μ := by
  have hi : Integrable (fun y => f y • fderiv ℝ κ (x - y)) μ := by
    apply (hf.smul ((hκ.continuous_fderiv one_ne_zero).comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
    exact hcf.smul_right
  have h := hcκ.hasFDerivAt_convolution_right (μ := μ) (ContinuousLinearMap.mul ℝ ℝ)
    hf.locallyIntegrable hκ x
  change HasFDerivAt (scalarConvolution μ κ f) _ x at h
  rw [h.fderiv]
  change (∫ y, (ContinuousLinearMap.precompR E (ContinuousLinearMap.mul ℝ ℝ)) (f y)
    (fderiv ℝ κ (x - y)) ∂μ) v = _
  have he : (fun y => (ContinuousLinearMap.precompR E (ContinuousLinearMap.mul ℝ ℝ)) (f y)
      (fderiv ℝ κ (x - y))) = fun y => f y • fderiv ℝ κ (x - y) := by
    funext y
    ext w
    rfl
  rw [he, ContinuousLinearMap.integral_apply hi v]
  rfl

end TernaryPoly.CompactCoordinateIntegration
