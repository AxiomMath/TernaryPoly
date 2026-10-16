module

public import TernaryPeriodPolynomials.Analysis.Compact.Scalar.Mollifier
public import TernaryPeriodPolynomials.Analysis.Compact.Scalar.Approximation
public import TernaryPeriodPolynomials.Analysis.Compact.Scalar.ConvolutionBounds
public import TernaryPeriodPolynomials.Analysis.Compact.DominatedSquareConvergence
public import TernaryPeriodPolynomials.Analysis.Compact.Scalar.Bound

@[expose] public section


/-! Strong square-integral convergence of genuine normalized mollification under a compact cutoff. -/
noncomputable section
namespace TernaryPoly.CompactCoordinateIntegration
open MeasureTheory Filter CompactScalarMollifier
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

theorem cutoff_mollifier_square_tendsto (f η : E → ℝ) (hf : Continuous f)
    (hcf : HasCompactSupport f) (hη : Continuous η) (hcη : HasCompactSupport η) :
    Tendsto (fun c : ℝ => ∫ x, ‖η x * (scalarConvolution μ (kernel E μ c) f x - f x)‖^2 ∂μ)
      atTop (nhds 0) := by
  obtain ⟨M,hM,hMb⟩ := CompactScalarBound.exists_bound f hf hcf
  obtain ⟨N,hN,hNb⟩ := CompactScalarBound.exists_bound η hη hcη
  let u (c : ℝ) (x : E) := η x * (scalarConvolution μ (kernel E μ c) f x - f x)
  have hc (c : ℝ) (hc : 0 < c) : Continuous (u c) :=
    hη.mul (((contDiff_scalarConvolution μ _ f (kernel_contDiff E μ c)
      (kernel_compact E μ c hc.ne') hf).continuous).sub hf)
  have hb (c : ℝ) (hc : 0 < c) (x : E) : ‖u c x‖ ≤ N*(2*M) := by
    have hki : Integrable (kernel E μ c) μ := (kernel_contDiff E μ c).continuous.integrable_of_hasCompactSupport (kernel_compact E μ c hc.ne')
    have hconv := norm_scalarConvolution_le_mass μ (kernel E μ c) f hki
      (kernel_nonneg E μ c hc.le) M hMb x
    rw [kernel_integral E μ c hc,one_mul] at hconv
    have hd : ‖scalarConvolution μ (kernel E μ c) f x - f x‖ ≤ 2*M :=
      (norm_sub_le _ _).trans (by linarith [hMb x])
    exact (norm_mul _ _).le.trans (mul_le_mul (hNb x) hd (norm_nonneg _) hN)
  apply CompactDominatedSquareConvergence.integral_norm_square_tendsto_zero u (tsupport η)
    (isClosed_tsupport _).measurableSet hcη.measure_lt_top.ne (N*(2*M)) (by positivity)
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with c hcpos
    exact (hc c hcpos).aestronglyMeasurable
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with c hcpos
    exact hb c hcpos
  · exact Filter.Eventually.of_forall (fun c x hx => by
      simp only [u,image_eq_zero_of_notMem_tsupport hx,zero_mul])
  · intro x
    have h := scalarConvolution_dilate_tendsto μ ((bump E).normed μ) f
      (bump E).nonneg_normed (bump E).integral_normed (bump E).hasCompactSupport_normed
      (hf.integrable_of_hasCompactSupport hcf) x hf.continuousAt
    simpa only [u, kernel, mul_zero, sub_self] using
      ((tendsto_const_nhds (x := η x)).mul (h.sub (tendsto_const_nhds (x := f x))))

end TernaryPoly.CompactCoordinateIntegration
