module

public import TernaryPeriodPolynomials.Analysis.Compact.Scalar.Convolution
public import Mathlib.Analysis.Calculus.ContDiff.Convolution

@[expose] public section


/-! Smoothness and genuine support control for local scalar convolution. -/
noncomputable section
namespace TernaryPoly.CompactCoordinateIntegration
open MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

theorem contDiff_scalarConvolution {n : ℕ∞} (κ f : E → ℝ)
    (hκ : ContDiff ℝ n κ) (hcκ : HasCompactSupport κ) (hf : Continuous f) :
    ContDiff ℝ n (scalarConvolution μ κ f) :=
  hcκ.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℝ) hf.locallyIntegrable hκ

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure] in
theorem compact_scalarConvolution (κ f : E → ℝ)
    (hcκ : HasCompactSupport κ) (hcf : HasCompactSupport f) :
    HasCompactSupport (scalarConvolution μ κ f) :=
  hcf.convolution (ContinuousLinearMap.mul ℝ ℝ) hcκ

end TernaryPoly.CompactCoordinateIntegration
