module

public import TernaryPeriodPolynomials.Analysis.Compact.Scalar.Approximation

@[expose] public section


/-! Actual strong-on-smooth-input precursor: pointwise vanishing of the derivative commutator. -/
noncomputable section
namespace TernaryPoly.CompactCoordinateIntegration
open MeasureTheory Filter ScaledScalarKernel
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

/-- The actual first-order commutator tends to zero on every compact C1 input at every point. -/
theorem firstOrder_convolution_commutator_tendsto (κ a b f : E → ℝ) (v x : E)
    (hκ : ContDiff ℝ 1 κ) (hcκ : HasCompactSupport κ)
    (hκnonneg : ∀ y, 0 ≤ κ y) (hmass : ∫ y, κ y ∂μ = 1)
    (ha : Continuous a) (hb : Continuous b) (hf : ContDiff ℝ 1 f) (hcf : HasCompactSupport f) :
    Tendsto (fun c : ℝ => firstOrder v a b (scalarConvolution μ (dilate c κ) f) x -
      scalarConvolution μ (dilate c κ) (firstOrder v a b f) x) atTop (nhds 0) := by
  have hdf : Continuous (fun y => fderiv ℝ f y v) :=
    (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hDf := continuous_firstOrder v ha hb hf
  have ht0 := scalarConvolution_dilate_tendsto μ κ f hκnonneg hmass hcκ
    (hf.continuous.integrable_of_hasCompactSupport hcf) x hf.continuous.continuousAt
  have ht1 := scalarConvolution_dilate_tendsto μ κ (fun y => fderiv ℝ f y v)
    hκnonneg hmass hcκ (hdf.integrable_of_hasCompactSupport (hcf.fderiv_apply ℝ v)) x hdf.continuousAt
  have htD := scalarConvolution_dilate_tendsto μ κ (firstOrder v a b f)
    hκnonneg hmass hcκ (hDf.integrable_of_hasCompactSupport (compact_firstOrder v a b hcf)) x hDf.continuousAt
  have h := ((ht1.const_mul (a x)).add (ht0.const_mul (b x))).sub htD
  simp only [firstOrder, sub_self] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with c hc
  rw [firstOrder, fderiv_scalarConvolution_eq_input μ (dilate c κ) f
    (contDiff_dilate κ c hκ).continuous (compact_dilate κ c hc.ne' hcκ) hf hcf]

end TernaryPoly.CompactCoordinateIntegration
