module

public import TernaryPeriodPolynomials.Analysis.Compact.Scalar.Convolution

@[expose] public section


/-! The actual derivative commutator formula for variable-coefficient first-order convolution. -/
noncomputable section
namespace TernaryPoly.CompactCoordinateIntegration
open MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Differentiate the reflected convolution kernel in the integration variable. -/
theorem fderiv_reflectedKernel (κ : E → ℝ) (x y v : E) (hκ : DifferentiableAt ℝ κ (x - y)) :
    fderiv ℝ (fun z => κ (x - z)) y v = -fderiv ℝ κ (x - y) v := by
  have hh : HasFDerivAt (fun z => κ (x - z))
      ((fderiv ℝ κ (x - y)).comp (-(ContinuousLinearMap.id ℝ E))) y :=
    hκ.hasFDerivAt.comp y ((hasFDerivAt_id y).const_sub x)
  rw [hh.fderiv]
  simp

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The literal transpose divergence applied to the translated kernel. -/
theorem transposeOrder_reflectedKernel (κ a b : E → ℝ) (x y v : E)
    (ha : DifferentiableAt ℝ a y) (hκ : DifferentiableAt ℝ κ (x - y)) :
    transposeOrder v a b (fun z => κ (x - z)) y =
      b y * κ (x - y) - fderiv ℝ a y v * κ (x - y) + a y * fderiv ℝ κ (x - y) v := by
  have hkd : DifferentiableAt ℝ (fun z => κ (x - z)) y :=
    hκ.comp y ((differentiableAt_id).const_sub x)
  unfold transposeOrder
  rw [fderiv_fun_mul ha hkd]
  simp only [add_apply, smul_apply, smul_eq_mul]
  rw [fderiv_reflectedKernel κ x y v hκ]
  ring

/-- Move a genuine first-order operator off the compact input by actual integration by parts. -/
theorem scalarConvolution_firstOrder (κ a b f : E → ℝ) (v x : E)
    (ha : ContDiff ℝ 1 a) (hb : Continuous b) (hf : ContDiff ℝ 1 f)
    (hκ : ContDiff ℝ 1 κ) (hcf : HasCompactSupport f) :
    scalarConvolution μ κ (firstOrder v a b f) x =
      ∫ y, f y * transposeOrder v a b (fun z => κ (x - z)) y ∂μ := by
  exact integral_firstOrder_mul v ha hb hf (hκ.comp (contDiff_const.sub contDiff_id)) hcf

/-- The full first-order Friedrichs commutator, including the derivative of the coefficient.
This is an exact identity on genuine compact smooth inputs, not only a multiplication commutator. -/
theorem firstOrder_convolution_commutator (κ a b f : E → ℝ) (v x : E)
    (ha : ContDiff ℝ 1 a) (hb : Continuous b) (hf : ContDiff ℝ 1 f)
    (hκ : ContDiff ℝ 1 κ) (hcf : HasCompactSupport f) (hcκ : HasCompactSupport κ) :
    firstOrder v a b (scalarConvolution μ κ f) x - scalarConvolution μ κ (firstOrder v a b f) x =
      ∫ y, f y * ((a x - a y) * fderiv ℝ κ (x - y) v +
        (fderiv ℝ a y v + b x - b y) * κ (x - y)) ∂μ := by
  have hg : ContDiff ℝ 1 (fun y => κ (x - y)) := hκ.comp (contDiff_const.sub contDiff_id)
  have h0 : Integrable (fun y => f y * κ (x - y)) μ :=
    (hf.continuous.mul hg.continuous).integrable_of_hasCompactSupport hcf.mul_right
  have h1 : Integrable (fun y => f y * fderiv ℝ κ (x - y) v) μ :=
    (hf.continuous.mul (((hκ.continuous_fderiv one_ne_zero).comp
      (continuous_const.sub continuous_id)).clm_apply continuous_const)).integrable_of_hasCompactSupport hcf.mul_right
  have ht : Integrable (fun y => f y * transposeOrder v a b (fun z => κ (x - z)) y) μ :=
    (hf.continuous.mul (continuous_transposeOrder v ha hb hg)).integrable_of_hasCompactSupport hcf.mul_right
  have hs : Integrable (fun y => a x * (f y * fderiv ℝ κ (x-y) v) + b x * (f y * κ (x-y))) μ :=
    (h1.const_mul (a x)).add (h0.const_mul (b x))
  rw [firstOrder, fderiv_scalarConvolution μ κ f hκ hcκ hf.continuous hcf,
    scalarConvolution_apply, scalarConvolution_firstOrder μ κ a b f v x ha hb hf hκ hcf,
    ← integral_const_mul, ← integral_const_mul,
    ← integral_add (h1.const_mul (a x)) (h0.const_mul (b x)),
    ← integral_sub hs ht]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro y
  dsimp only
  rw [transposeOrder_reflectedKernel κ a b x y v
    (ha.differentiable one_ne_zero y) (hκ.differentiable one_ne_zero (x - y))]
  ring

end TernaryPoly.CompactCoordinateIntegration
