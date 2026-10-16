module

public import TernaryPeriodPolynomials.Analysis.Compact.FirstOrderCutoffConvolution
public import TernaryPeriodPolynomials.Analysis.Compact.Scalar.CommutatorRegularity

@[expose] public section


/-! The exact output-cutoff commutator includes its principal-symbol cutoff term. -/
noncomputable section
namespace TernaryPoly.CompactCoordinateIntegration
open MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

theorem cutoff_convolution_commutator (v : E) (κ a b η f : E → ℝ)
    (hκ : ContDiff ℝ 1 κ) (hcκ : HasCompactSupport κ)
    (hη : ContDiff ℝ 1 η) (hf : Continuous f) (x : E) :
    firstOrder v a b (fun y => η y * scalarConvolution μ κ f y) x -
      η x * scalarConvolution μ κ (firstOrder v a b f) x =
      η x * scalarCommutator μ κ v a b f x +
        (a x * fderiv ℝ η x v) * scalarConvolution μ κ f x := by
  rw [firstOrder_mul v a b η _ x (hη.differentiable one_ne_zero x)
    ((contDiff_scalarConvolution μ κ f hκ hcκ hf).differentiable one_ne_zero x)]
  simp only [firstOrder, scalarCommutator]
  ring

end TernaryPoly.CompactCoordinateIntegration
