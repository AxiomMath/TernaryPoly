module

public import TernaryPeriodPolynomials.Analysis.Compact.Scalar.MollifierApproximation
public import TernaryPeriodPolynomials.Analysis.Finite.CoordinateIntegral
public import TernaryPeriodPolynomials.Analysis.Compact.SquareIntegral

@[expose] public section

/-! Genuine finite-vector L2 convergence of normalized compactly localized mollification. -/
noncomputable section
namespace TernaryPoly.CompactCoordinateIntegration
open MeasureTheory Filter CompactScalarMollifier CompactSquareIntegral
variable {E F I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [Fintype I]
  (μ : Measure E) [μ.IsAddHaarMeasure]

theorem cutoff_finite_mollifier_square_tendsto (e : F ≃L[ℝ] (I → ℝ))
    (f : I → E → ℝ) (hf : ∀ i, Continuous (f i)) (hcf : ∀ i, HasCompactSupport (f i))
    (η : E → ℝ) (hη : Continuous η) (hcη : HasCompactSupport η) :
    Tendsto (fun c : ℝ => ∫ x,
      ‖η x • (e.symm (fun i => scalarConvolution μ (kernel E μ c) (f i) x) -
        e.symm (fun i => f i x))‖^2 ∂μ) atTop (nhds 0) := by
  let z (c : ℝ) (x : E) := η x • (e.symm (fun i => scalarConvolution μ (kernel E μ c) (f i) x) -
    e.symm (fun i => f i x))
  let u (i : I) (c : ℝ) (x : E) := η x * (scalarConvolution μ (kernel E μ c) (f i) x - f i x)
  have he (c : ℝ) (x : E) (i : I) : e (z c x) i = u i c x := by
    simp only [z,u,map_smul,map_sub,e.apply_symm_apply,Pi.smul_apply,Pi.sub_apply,smul_eq_mul]
  have hc (c : ℝ) (h : 0 < c) (i : I) : Continuous (fun x => scalarConvolution μ (kernel E μ c) (f i) x) :=
    (contDiff_scalarConvolution μ _ _ (kernel_contDiff E μ c) (kernel_compact E μ c h.ne') (hf i)).continuous
  have huc (c : ℝ) (h : 0 < c) (i : I) : Continuous (u i c) := hη.mul ((hc c h i).sub (hf i))
  have hi (c : ℝ) (h : 0 < c) (i : I) : Integrable (fun x => ‖e (z c x) i‖^2) μ := by
    simp_rw [he]
    exact integrable_norm_square _ (huc c h i) hcη.mul_right
  have hbound : ∀ᶠ c : ℝ in atTop, (∫ x, ‖z c x‖^2 ∂μ) ≤
      ‖e.symm.toContinuousLinearMap‖^2 * ∑ i, ∫ x, ‖u i c x‖^2 ∂μ := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with c h
    have hzc : Continuous (z c) := hη.smul
      ((e.symm.continuous.comp (continuous_pi (hc c h))).sub (e.symm.continuous.comp (continuous_pi hf)))
    have hzi := integrable_norm_square (μ := μ) (z c) hzc hcη.smul_right
    have hb := FiniteCoordinateSquare.integral_square_le_coordinates e (z c) hzi (hi c h)
    simpa only [he] using hb
  have ht (i : I) : Tendsto (fun c => ∫ x, ‖u i c x‖^2 ∂μ) atTop (nhds 0) :=
    cutoff_mollifier_square_tendsto μ (f i) η (hf i) (hcf i) hη hcη
  have hlim : Tendsto (fun c => ‖e.symm.toContinuousLinearMap‖^2 * ∑ i, ∫ x, ‖u i c x‖^2 ∂μ)
      atTop (nhds 0) := by
    simpa using (tendsto_finsetSum Finset.univ (fun i _ => ht i)).const_mul (‖e.symm.toContinuousLinearMap‖^2)
  exact squeeze_zero' (Eventually.of_forall (fun c => integral_nonneg (fun x => sq_nonneg _))) hbound hlim

end TernaryPoly.CompactCoordinateIntegration
