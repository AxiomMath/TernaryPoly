module

public import TernaryPeriodPolynomials.Analysis.Compact.Matrix.DoubleCutoffIdentity
public import TernaryPeriodPolynomials.Analysis.Compact.DoubleCutoffCommutatorConvergence
public import TernaryPeriodPolynomials.Analysis.Finite.IntegralSquare

@[expose] public section


/-! Localized matrix commutators converge to their full principal-symbol cutoff term. -/
noncomputable section
namespace TernaryPoly.CompactScalarMollifier
open MeasureTheory Filter CompactCoordinateIntegration
variable {E I J K : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure] [Fintype I] [Fintype K]

theorem matrix_double_cutoff_tendsto (χ η : E → ℝ) (hχ : ContDiff ℝ 1 χ) (hcχ : HasCompactSupport χ)
    (hη : ContDiff ℝ 1 η) (hcη : HasCompactSupport η)
    (v : K → E) (a b : J → I → K → E → ℝ)
    (ha : ∀ j i k, ContDiff ℝ 1 (a j i k)) (hb : ∀ j i k, Continuous (b j i k))
    (hca : ∀ j i k, HasCompactSupport (a j i k)) (hcb : ∀ j i k, HasCompactSupport (b j i k))
    (f : I → E → ℝ) (hf : ∀ i, ContDiff ℝ 1 (f i)) (j : J) :
    Tendsto (fun c : ℝ => ∫ x, ‖
      (matrixFirstOrder v a b (fun i y => η y * scalarConvolution μ (kernel E μ c) (fun z => χ z * f i z) y) j x -
        η x * scalarConvolution μ (kernel E μ c) (fun z => χ z * matrixFirstOrder v a b f j z) x) -
      ∑ i, ∑ k, ((a j i k x * fderiv ℝ η x (v k)) * (χ x * f i x) +
        η x * ((a j i k x * fderiv ℝ χ x (v k)) * f i x))‖^2 ∂μ) atTop (nhds 0) := by
  let L (p : I × K) (x : E) := (a j p.1 p.2 x * fderiv ℝ η x (v p.2)) * (χ x * f p.1 x) +
    η x * ((a j p.1 p.2 x * fderiv ℝ χ x (v p.2)) * f p.1 x)
  let u (p : I × K) (c : ℝ) (x : E) :=
    doubleCutoffCommutator μ (kernel E μ c) (v p.2) (a j p.1 p.2) (b j p.1 p.2) χ η (f p.1) x - L p x
  have hL (p : I × K) : Continuous (L p) :=
    (((ha j p.1 p.2).continuous.mul ((hη.continuous_fderiv one_ne_zero).clm_apply continuous_const)).mul
      (hχ.continuous.mul (hf p.1).continuous)).add
      (hη.continuous.mul (((ha j p.1 p.2).continuous.mul ((hχ.continuous_fderiv one_ne_zero).clm_apply continuous_const)).mul (hf p.1).continuous))
  have hcL (p : I × K) : HasCompactSupport (L p) :=
    ((hcη.fderiv_apply ℝ (v p.2)).mul_left.mul_right).add hcη.mul_right
  have hm (p : I × K) : ∀ᶠ c : ℝ in atTop, AEStronglyMeasurable (u p c) μ := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with c hc
    exact ((continuous_doubleCutoffCommutator μ _ _ _ _ _ _ _
      ((kernel_contDiff E μ c).of_le (by simp)) (kernel_compact E μ c hc.ne')
      (ha j p.1 p.2).continuous (hb j p.1 p.2) hχ.continuous hη (hf p.1)).sub (hL p)).aestronglyMeasurable
  have hi (p : I × K) : ∀ᶠ c : ℝ in atTop, Integrable (fun x => u p c x ^ 2) μ := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with c hc
    have H := CompactSquareIntegral.integrable_norm_square (u p c)
      ((continuous_doubleCutoffCommutator μ _ _ _ _ _ _ _ ((kernel_contDiff E μ c).of_le (by simp))
        (kernel_compact E μ c hc.ne') (ha j p.1 p.2).continuous (hb j p.1 p.2) hχ.continuous hη (hf p.1)).sub (hL p))
      ((compact_doubleCutoffCommutator μ _ _ _ _ _ _ _ hcη).sub (hcL p)) (μ := μ)
    simpa only [Real.norm_eq_abs, sq_abs] using H
  have ht (p : I × K) : Tendsto (fun c : ℝ => ∫ x, u p c x ^ 2 ∂μ) atTop (nhds 0) := by
    have H := double_cutoff_commutator_tendsto μ (v p.2) (a j p.1 p.2) (b j p.1 p.2) χ η (f p.1)
      (ha j p.1 p.2) (hb j p.1 p.2) (hca j p.1 p.2) (hcb j p.1 p.2) hχ hcχ hη hcη (hf p.1)
    simpa only [u,L,Real.norm_eq_abs,sq_abs] using H
  have H := FiniteIntegralSquare.integral_sum_square_tendsto_zero Finset.univ u
    (fun p _ => hm p) (fun p _ => hi p) (fun p _ => ht p)
  have he (c : ℝ) (x : E) :
      (matrixFirstOrder v a b (fun i y => η y * scalarConvolution μ (kernel E μ c) (fun z => χ z * f i z) y) j x -
        η x * scalarConvolution μ (kernel E μ c) (fun z => χ z * matrixFirstOrder v a b f j z) x) -
      ∑ i, ∑ k, L (i,k) x = ∑ p : I × K, u p c x := by
    rw [matrix_double_cutoff_commutator μ _ χ η v a b f (kernel_contDiff E μ c).continuous
      (fun j i k => (ha j i k).continuous) hb hχ.continuous hcχ hf]
    simp only [Fintype.sum_prod_type, u, Finset.sum_sub_distrib]
  change Tendsto (fun c : ℝ => ∫ x, ‖_ - ∑ i, ∑ k, L (i,k) x‖^2 ∂μ) atTop (nhds 0)
  simp_rw [he,Real.norm_eq_abs,sq_abs]
  exact H

end TernaryPoly.CompactScalarMollifier
