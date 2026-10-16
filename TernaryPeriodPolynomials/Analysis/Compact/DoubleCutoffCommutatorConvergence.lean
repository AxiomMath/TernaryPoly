module

public import TernaryPeriodPolynomials.Analysis.Compact.DoubleCutoffCommutatorRegularity
public import TernaryPeriodPolynomials.Analysis.Compact.Scalar.MollifierCore
public import TernaryPeriodPolynomials.Analysis.Compact.Scalar.MollifierApproximation
public import TernaryPeriodPolynomials.Analysis.Compact.SquareConvergence

@[expose] public section


/-! The localized commutator converges to both genuine cutoff derivative terms. -/
noncomputable section
namespace TernaryPoly.CompactScalarMollifier
open MeasureTheory Filter CompactCoordinateIntegration CompactSquareIntegral
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

theorem double_cutoff_commutator_tendsto (v : E) (a b χ η f : E → ℝ)
    (ha : ContDiff ℝ 1 a) (hb : Continuous b) (hca : HasCompactSupport a) (hcb : HasCompactSupport b)
    (hχ : ContDiff ℝ 1 χ) (hcχ : HasCompactSupport χ)
    (hη : ContDiff ℝ 1 η) (hcη : HasCompactSupport η) (hf : ContDiff ℝ 1 f) :
    Tendsto (fun c : ℝ => ∫ x, ‖doubleCutoffCommutator μ (kernel E μ c) v a b χ η f x -
      ((a x * fderiv ℝ η x v) * (χ x * f x) + η x * ((a x * fderiv ℝ χ x v) * f x))‖^2 ∂μ)
      atTop (nhds 0) := by
  let g : E → ℝ := fun x => χ x * f x
  let A : E → ℝ := fun x => a x * fderiv ℝ η x v
  let h : E → ℝ := fun x => (a x * fderiv ℝ χ x v) * f x
  have hg : ContDiff ℝ 1 g := hχ.mul hf
  have hcg : HasCompactSupport g := hcχ.mul_right
  have hA : Continuous A := ha.continuous.mul ((hη.continuous_fderiv one_ne_zero).clm_apply continuous_const)
  have hcA : HasCompactSupport A := (hcη.fderiv_apply ℝ v).mul_left
  have hh : Continuous h := (ha.continuous.mul ((hχ.continuous_fderiv one_ne_zero).clm_apply continuous_const)).mul hf.continuous
  have hch : HasCompactSupport h := (hcχ.fderiv_apply ℝ v).mul_left.mul_right
  let s : ℝ → E → ℝ := fun c x => η x * scalarCommutator μ (kernel E μ c) v a b g x
  let t : ℝ → E → ℝ := fun c x => A x * (scalarConvolution μ (kernel E μ c) g x - g x)
  let r : ℝ → E → ℝ := fun c x => η x * (scalarConvolution μ (kernel E μ c) h x - h x)
  have hz (c : ℝ) (hc : 0 < c) : Continuous (scalarCommutator μ (kernel E μ c) v a b g) :=
    continuous_scalarCommutator μ _ _ _ _ _ ((kernel_contDiff E μ c).of_le (by simp))
      (kernel_compact E μ c hc.ne') ha.continuous hb hg
  have hcz (c : ℝ) (hc : 0 < c) : HasCompactSupport (scalarCommutator μ (kernel E μ c) v a b g) :=
    compact_scalarCommutator μ _ _ _ _ _ (kernel_compact E μ c hc.ne') hcg
  have hts : Tendsto (fun c => ∫ x, ‖s c x‖^2 ∂μ) atTop (nhds 0) := by
    have H := (compact_coefficients_friedrichs μ a b v ha hb hca hcb).choose_spec.2.2 g hg hcg
    apply cutoff_square_tendsto_zero η hη.continuous hcη _ _ _ H
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with c hc
      exact hz c hc
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with c hc
      exact integrable_norm_square _ (hz c hc) (hcz c hc)
  have htt : Tendsto (fun c => ∫ x, ‖t c x‖^2 ∂μ) atTop (nhds 0) :=
    cutoff_mollifier_square_tendsto μ g A hg.continuous hcg hA hcA
  have htr : Tendsto (fun c => ∫ x, ‖r c x‖^2 ∂μ) atTop (nhds 0) :=
    cutoff_mollifier_square_tendsto μ h η hh hch hη.continuous hcη
  have hs : ∀ᶠ c in atTop, Continuous (s c) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with c hc
    exact hη.continuous.mul (hz c hc)
  have ht : ∀ᶠ c in atTop, Continuous (t c) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with c hc
    exact hA.mul ((contDiff_scalarConvolution μ _ g (kernel_contDiff E μ c) (kernel_compact E μ c hc.ne') hg.continuous).continuous.sub hg.continuous)
  have hr : ∀ᶠ c in atTop, Continuous (r c) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with c hc
    exact hη.continuous.mul ((contDiff_scalarConvolution μ _ h (kernel_contDiff E μ c) (kernel_compact E μ c hc.ne') hh).continuous.sub hh)
  have hcs : ∀ᶠ c : ℝ in atTop, HasCompactSupport (s c) := Eventually.of_forall (fun _ => hcη.mul_right)
  have hct : ∀ᶠ c : ℝ in atTop, HasCompactSupport (t c) := Eventually.of_forall (fun _ => hcA.mul_right)
  have hcr : ∀ᶠ c : ℝ in atTop, HasCompactSupport (r c) := Eventually.of_forall (fun _ => hcη.mul_right)
  have hst := integral_add_square_tendsto_zero s t hs ht hcs hct hts htt
  have hstr := integral_add_square_tendsto_zero (fun c x => s c x + t c x) r
    (hs.and ht |>.mono (fun _ hc => hc.1.add hc.2)) hr
    (hcs.and hct |>.mono (fun _ hc => hc.1.add hc.2)) hcr hst htr
  apply Tendsto.congr' _ hstr
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with c hc
  apply integral_congr_ae
  exact Eventually.of_forall (fun x => by
    have hd := double_cutoff_convolution_commutator μ v (kernel E μ c) a b χ η f
      (kernel_contDiff E μ c).continuous ha.continuous hb hχ hcχ hf x
    have ho := cutoff_convolution_commutator μ v (kernel E μ c) a b η g
      ((kernel_contDiff E μ c).of_le (by simp)) (kernel_compact E μ c hc.ne') hη hg.continuous x
    change ‖(s c x + t c x) + r c x‖^2 = _
    congr 2
    dsimp only [s,t,r,A,g,h]
    dsimp only [doubleCutoffCommutator]
    rw [hd]
    change _ = (firstOrder v a b (fun y => η y * scalarConvolution μ (kernel E μ c) g y) x -
      η x * scalarConvolution μ (kernel E μ c) (firstOrder v a b g) x) + _ - _
    rw [ho]
    dsimp only [g]
    ring)

end TernaryPoly.CompactScalarMollifier
