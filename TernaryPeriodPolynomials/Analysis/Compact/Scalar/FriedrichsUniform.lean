module

public import TernaryPeriodPolynomials.Analysis.Compact.Scalar.FriedrichsBound
public import TernaryPeriodPolynomials.Analysis.ScaledScalarKernelRegularity

@[expose] public section


/-! Uniform L2 bound for the actual first-order commutator at every positive smoothing scale. -/
noncomputable section
namespace TernaryPoly.CompactCoordinateIntegration
open MeasureTheory ScalarFriedrichsEnvelope ScaledScalarKernel
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

/-- The bound for the actual derivative commutator is independent of the dilation parameter. -/
theorem firstOrder_convolution_commutator_uniform (κ a b f : E → ℝ) (v : E)
    (ha : ContDiff ℝ 1 a) (hb : Continuous b) (hf : ContDiff ℝ 1 f)
    (hκ : ContDiff ℝ 1 κ) (hcf : HasCompactSupport f) (hcκ : HasCompactSupport κ)
    (L A B : ℝ) (hL : 0 ≤ L) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (haL : ∀ x y, ‖a x - a y‖ ≤ L * ‖x-y‖)
    (hda : ∀ y, ‖fderiv ℝ a y v‖ ≤ A) (hbB : ∀ y, ‖b y‖ ≤ B)
    (c : ℝ) (hc : 0 < c) :
    ∫ x, ‖firstOrder v a b (scalarConvolution μ (dilate c κ) f) x -
        scalarConvolution μ (dilate c κ) (firstOrder v a b f) x‖ ^ 2 ∂μ ≤
      (∫ z, envelope κ v L A B z ∂μ) ^ 2 * ∫ y, ‖f y‖ ^ 2 ∂μ := by
  have h := firstOrder_convolution_commutator_square_bound μ (dilate c κ) a b f v
    ha hb hf (contDiff_dilate κ c hκ) hcf (compact_dilate κ c hc.ne' hcκ)
    L A B hL hA hB haL hda hbB
  rwa [integral_envelope_dilate μ κ v L A B c hc (hκ.differentiable one_ne_zero)] at h

end TernaryPoly.CompactCoordinateIntegration
