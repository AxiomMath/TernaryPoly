module

public import TernaryPeriodPolynomials.Analysis.Compact.Scalar.FriedrichsUniform
public import TernaryPeriodPolynomials.Analysis.Compact.Scalar.ConvolutionBounds

@[expose] public section


/-! The actual commutator is dominated pointwise by a positive compact convolution. -/
noncomputable section
namespace TernaryPoly.CompactCoordinateIntegration
open MeasureTheory ScalarFriedrichsEnvelope ScaledScalarKernel
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

theorem norm_firstOrder_commutator_le_envelope (κ a b f : E → ℝ) (v x : E)
    (ha : ContDiff ℝ 1 a) (hb : Continuous b) (hf : ContDiff ℝ 1 f)
    (hκ : ContDiff ℝ 1 κ) (hcf : HasCompactSupport f) (hcκ : HasCompactSupport κ)
    (L A B : ℝ) (haL : ∀ y, ‖a x - a y‖ ≤ L * ‖x-y‖)
    (hda : ∀ y, ‖fderiv ℝ a y v‖ ≤ A) (hbB : ∀ y, ‖b y‖ ≤ B) :
    ‖firstOrder v a b (scalarConvolution μ κ f) x - scalarConvolution μ κ (firstOrder v a b f) x‖ ≤
      scalarConvolution μ (envelope κ v L A B) (fun y => ‖f y‖) x := by
  rw [firstOrder_convolution_commutator μ κ a b f v x ha hb hf hκ hcf hcκ, scalarConvolution_apply]
  have hi : Integrable (fun y => ‖f y‖ * envelope κ v L A B (x-y)) μ :=
    (hf.continuous.norm.mul ((continuous_envelope κ v L A B hκ).comp
      (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport hcf.norm.mul_right
  apply norm_integral_le_of_norm_le hi
  exact Filter.Eventually.of_forall (fun y => by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left
      (norm_commutatorKernel_le κ a b v x y L A B (haL y) (hda y) (hbB x) (hbB y)) (norm_nonneg _))

/-- The actual scaled commutator is dominated by the dilation of one fixed envelope. -/
theorem norm_firstOrder_commutator_dilate_le_envelope (κ a b f : E → ℝ) (v x : E)
    (ha : ContDiff ℝ 1 a) (hb : Continuous b) (hf : ContDiff ℝ 1 f)
    (hκ : ContDiff ℝ 1 κ) (hcf : HasCompactSupport f) (hcκ : HasCompactSupport κ)
    (L A B : ℝ) (haL : ∀ y, ‖a x - a y‖ ≤ L * ‖x-y‖)
    (hda : ∀ y, ‖fderiv ℝ a y v‖ ≤ A) (hbB : ∀ y, ‖b y‖ ≤ B) (c : ℝ) (hc : 0 < c) :
    ‖firstOrder v a b (scalarConvolution μ (dilate c κ) f) x -
      scalarConvolution μ (dilate c κ) (firstOrder v a b f) x‖ ≤
      scalarConvolution μ (dilate c (envelope κ v L A B)) (fun y => ‖f y‖) x := by
  have h := norm_firstOrder_commutator_le_envelope μ (dilate c κ) a b f v x ha hb hf
    (contDiff_dilate κ c hκ) hcf (compact_dilate κ c hc.ne' hcκ) L A B haL hda hbB
  have he : envelope (dilate c κ) v L A B = dilate c (envelope κ v L A B) := by
    funext z
    exact envelope_dilate κ v z L A B c hc (hκ.differentiable one_ne_zero)
  rwa [he] at h

end TernaryPoly.CompactCoordinateIntegration
