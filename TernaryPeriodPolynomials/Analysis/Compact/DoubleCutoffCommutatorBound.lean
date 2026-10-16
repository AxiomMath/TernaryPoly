module

public import TernaryPeriodPolynomials.Analysis.Compact.DoubleCutoffCommutatorIdentity
public import TernaryPeriodPolynomials.Analysis.Compact.CutoffCommutatorBound
public import TernaryPeriodPolynomials.Analysis.Compact.Scalar.Bound

@[expose] public section


/-! A single scale-independent bound for the actual two-cutoff first-order commutator. -/
noncomputable section
namespace TernaryPoly.CompactScalarMollifier
open MeasureTheory CompactCoordinateIntegration CompactSquareIntegral
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

theorem double_cutoff_commutator_uniform (v : E) (a b χ η : E → ℝ)
    (ha : ContDiff ℝ 1 a) (hb : Continuous b) (hca : HasCompactSupport a) (hcb : HasCompactSupport b)
    (hχ : ContDiff ℝ 1 χ) (hcχ : HasCompactSupport χ)
    (hη : ContDiff ℝ 1 η) (hcη : HasCompactSupport η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : E → ℝ, ContDiff ℝ 1 f → HasCompactSupport f →
      ∀ c : ℝ, 0 < c →
      ∫ x, ‖firstOrder v a b (fun y => η y * scalarConvolution μ (kernel E μ c) (fun z => χ z * f z) y) x -
        η x * scalarConvolution μ (kernel E μ c) (fun z => χ z * firstOrder v a b f z) x‖^2 ∂μ ≤
        C * ∫ x, ‖f x‖^2 ∂μ := by
  obtain ⟨C,hC,hbound⟩ := cutoff_commutator_uniform μ v a b η ha hb hca hcb hη hcη
  let A : E → ℝ := fun x => a x * fderiv ℝ χ x v
  have hA : Continuous A := ha.continuous.mul ((hχ.continuous_fderiv one_ne_zero).clm_apply continuous_const)
  have hcA : HasCompactSupport A := (hcχ.fderiv_apply ℝ v).mul_left
  obtain ⟨M,hM,hMb⟩ := CompactScalarBound.exists_bound χ hχ.continuous hcχ
  obtain ⟨N,hN,hNb⟩ := CompactScalarBound.exists_bound η hη.continuous hcη
  obtain ⟨P,hP,hPb⟩ := CompactScalarBound.exists_bound A hA hcA
  refine ⟨2 * (C*M^2 + N^2*P^2), mul_nonneg (by norm_num)
    (add_nonneg (mul_nonneg hC (sq_nonneg _)) (mul_nonneg (sq_nonneg _) (sq_nonneg _))), ?_⟩
  intro f hf hcf c hc
  let κ := kernel E μ c
  have hk : ContDiff ℝ 1 κ := (kernel_contDiff E μ c).of_le (by simp)
  have hck := kernel_compact E μ c hc.ne'
  let g : E → ℝ := fun x => χ x * f x
  let h : E → ℝ := fun x => A x * f x
  have hg : ContDiff ℝ 1 g := hχ.mul hf
  have hcg : HasCompactSupport g := hcχ.mul_right
  have hh : Continuous h := hA.mul hf.continuous
  have hch : HasCompactSupport h := hcA.mul_right
  let u := scalarConvolution μ κ g
  have hu : ContDiff ℝ 1 u := contDiff_scalarConvolution μ κ g hk hck hg.continuous
  let q : E → ℝ := fun x => firstOrder v a b (fun y => η y * u y) x -
    η x * scalarConvolution μ κ (firstOrder v a b g) x
  have hq : Continuous q :=
    (continuous_firstOrder v ha.continuous hb (hη.mul hu)).sub
      (hη.continuous.mul ((contDiff_scalarConvolution μ κ (firstOrder v a b g) hk hck
        (continuous_firstOrder v ha.continuous hb hg)).continuous))
  have hcq : HasCompactSupport q :=
    (compact_firstOrder v a b hcη.mul_right).sub hcη.mul_right
  let r : E → ℝ := fun x => η x * scalarConvolution μ κ h x
  have hconv : Continuous (scalarConvolution μ κ h) := (contDiff_scalarConvolution μ κ h hk hck hh).continuous
  have hcconv := compact_scalarConvolution μ κ h hck hch
  have hr : Continuous r := hη.continuous.mul hconv
  have hcr : HasCompactSupport r := hcη.mul_right
  have hfi := integrable_norm_square f hf.continuous hcf (μ := μ)
  have hg2 := cutoff_square_le χ f hχ.continuous hcχ hf.continuous hfi M hM hMb
  have hh2 := cutoff_square_le A f hA hcA hf.continuous hfi P hP hPb
  have hq2 : (∫ x, ‖q x‖^2 ∂μ) ≤ C * (M^2 * ∫ x, ‖f x‖^2 ∂μ) :=
    (hbound g hg hcg c hc).trans (mul_le_mul_of_nonneg_left hg2 hC)
  have hr2 : (∫ x, ‖r x‖^2 ∂μ) ≤ N^2 * (P^2 * ∫ x, ‖f x‖^2 ∂μ) := by
    have hhconv := (mollifier_square_le μ c hc h hh hch).trans hh2
    exact (cutoff_square_le η _ hη.continuous hcη hconv
      (integrable_norm_square _ hconv hcconv (μ := μ)) N hN hNb).trans
      (mul_le_mul_of_nonneg_left hhconv (sq_nonneg N))
  have he (x : E) := double_cutoff_convolution_commutator μ v κ a b χ η f hk.continuous
    ha.continuous hb hχ hcχ hf x
  have heq : (fun x => firstOrder v a b (fun y => η y * scalarConvolution μ (kernel E μ c) (fun z => χ z * f z) y) x -
      η x * scalarConvolution μ (kernel E μ c) (fun z => χ z * firstOrder v a b f z) x) =
      (fun x => q x + r x) := funext he
  rw [show (∫ x, ‖firstOrder v a b (fun y => η y * scalarConvolution μ (kernel E μ c) (fun z => χ z * f z) y) x -
      η x * scalarConvolution μ (kernel E μ c) (fun z => χ z * firstOrder v a b f z) x‖^2 ∂μ) =
      (∫ x, ‖q x + r x‖^2 ∂μ) from congrArg (fun g : E → ℝ => ∫ x, ‖g x‖^2 ∂μ) heq]
  calc
    _ ≤ 2 * ((∫ x, ‖q x‖^2 ∂μ) + ∫ x, ‖r x‖^2 ∂μ) := integral_add_square_le q r hq hr hcq hcr
    _ ≤ 2 * (C * (M^2 * ∫ x, ‖f x‖^2 ∂μ) + N^2 * (P^2 * ∫ x, ‖f x‖^2 ∂μ)) :=
      mul_le_mul_of_nonneg_left (add_le_add hq2 hr2) (by norm_num)
    _ = _ := by ring

end TernaryPoly.CompactScalarMollifier
