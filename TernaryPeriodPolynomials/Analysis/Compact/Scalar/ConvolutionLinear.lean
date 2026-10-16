module

public import TernaryPeriodPolynomials.Analysis.Compact.Scalar.ConvolutionRegularity

@[expose] public section


/-! Actual additive and scalar laws of compact scalar convolution. -/
noncomputable section
namespace TernaryPoly.CompactCoordinateIntegration
open MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
theorem scalarConvolution_add (κ f g : E → ℝ) (hκ : Continuous κ)
    (hf : Continuous f) (hg : Continuous g) (hcf : HasCompactSupport f) (hcg : HasCompactSupport g) :
    scalarConvolution μ κ (f+g) = scalarConvolution μ κ f + scalarConvolution μ κ g := by
  funext x
  simp only [scalarConvolution_apply, Pi.add_apply, add_mul]
  apply integral_add
  · exact (hf.mul (hκ.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport hcf.mul_right
  · exact (hg.mul (hκ.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport hcg.mul_right

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure] in
theorem scalarConvolution_smul (κ f : E → ℝ) (a : ℝ) :
    scalarConvolution μ κ (a • f) = a • scalarConvolution μ κ f := by
  funext x
  simp only [scalarConvolution_apply, Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]

end TernaryPoly.CompactCoordinateIntegration
