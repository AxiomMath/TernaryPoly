module

public import TernaryPeriodPolynomials.Analysis.Compact.Scalar.Convolution

@[expose] public section


/-! Exact linearity of the actual scalar smoothing operator over finite compact families. -/
noncomputable section
namespace TernaryPoly.CompactCoordinateIntegration
open MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
theorem scalarConvolution_finsetSum {I : Type*} (s : Finset I) (κ : E → ℝ) (f : I → E → ℝ)
    (hκ : Continuous κ) (hf : ∀ i ∈ s, Continuous (f i))
    (hcf : ∀ i ∈ s, HasCompactSupport (f i)) (x : E) :
    scalarConvolution μ κ (fun y => ∑ i ∈ s, f i y) x = ∑ i ∈ s, scalarConvolution μ κ (f i) x := by
  simp only [scalarConvolution_apply, Finset.sum_mul]
  apply integral_finsetSum
  intro i hi
  exact ((hf i hi).mul (hκ.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
    (hcf i hi).mul_right

end TernaryPoly.CompactCoordinateIntegration
