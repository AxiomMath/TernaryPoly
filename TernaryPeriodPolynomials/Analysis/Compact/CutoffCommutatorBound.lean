module

public import TernaryPeriodPolynomials.Analysis.Compact.CutoffCommutatorIdentity
public import TernaryPeriodPolynomials.Analysis.Compact.Scalar.MollifierCore
public import TernaryPeriodPolynomials.Analysis.Compact.Scalar.ConvolutionSquare
public import TernaryPeriodPolynomials.Analysis.Compact.SquareSum

@[expose] public section

/-! Output-cutoff first-order commutators have a genuine uniform bound, including the cutoff term. -/
noncomputable section
namespace TernaryPoly.CompactScalarMollifier
open MeasureTheory CompactCoordinateIntegration CompactSquareIntegral
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

theorem cutoff_commutator_uniform (v : E) (a b η : E → ℝ)
    (ha : ContDiff ℝ 1 a) (hb : Continuous b) (hca : HasCompactSupport a) (hcb : HasCompactSupport b)
    (hη : ContDiff ℝ 1 η) (hcη : HasCompactSupport η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : E → ℝ, ContDiff ℝ 1 f → HasCompactSupport f →
      ∀ c : ℝ, 0 < c →
      ∫ x, ‖firstOrder v a b (fun y => η y * scalarConvolution μ (kernel E μ c) f y) x -
        η x * scalarConvolution μ (kernel E μ c) (firstOrder v a b f) x‖^2 ∂μ ≤
        C * ∫ x, ‖f x‖^2 ∂μ := by
  obtain ⟨C,hC,hbound,_⟩ := compact_coefficients_friedrichs μ a b v ha hb hca hcb
  let A : E → ℝ := fun x => a x * fderiv ℝ η x v
  have hA : Continuous A := ha.continuous.mul ((hη.continuous_fderiv one_ne_zero).clm_apply continuous_const)
  have hcA : HasCompactSupport A := (hcη.fderiv_apply ℝ v).mul_left
  obtain ⟨M,hM⟩ := (hcη.isCompact_range hη.continuous).isBounded.exists_norm_le
  obtain ⟨N,hN⟩ := (hcA.isCompact_range hA).isBounded.exists_norm_le
  have hM0 : 0 ≤ M := (norm_nonneg (η 0)).trans (hM _ ⟨0,rfl⟩)
  have hN0 : 0 ≤ N := (norm_nonneg (A 0)).trans (hN _ ⟨0,rfl⟩)
  refine ⟨2 * (M^2*C + N^2), mul_nonneg (by norm_num) (add_nonneg (mul_nonneg (sq_nonneg _) hC) (sq_nonneg _)), ?_⟩
  intro f hf hcf c hc
  let z := scalarCommutator μ (kernel E μ c) v a b f
  let u := scalarConvolution μ (kernel E μ c) f
  have hk : ContDiff ℝ 1 (kernel E μ c) := (kernel_contDiff E μ c).of_le (by simp)
  have hck := kernel_compact E μ c hc.ne'
  have hz : Continuous z := continuous_scalarCommutator μ _ _ _ _ _ hk hck ha.continuous hb hf
  have hcz : HasCompactSupport z := compact_scalarCommutator μ _ _ _ _ _ hck hcf
  have hu : Continuous u := (contDiff_scalarConvolution μ _ f hk hck hf.continuous).continuous
  have hcu : HasCompactSupport u := compact_scalarConvolution μ _ f hck hcf
  have hz2 := cutoff_square_le η z hη.continuous hcη hz (integrable_norm_square z hz hcz (μ := μ))
    M hM0 (fun x => hM _ ⟨x,rfl⟩)
  have hu2 := cutoff_square_le A u hA hcA hu (integrable_norm_square u hu hcu (μ := μ))
    N hN0 (fun x => hN _ ⟨x,rfl⟩)
  have hsum := integral_add_square_le (fun x => η x * z x) (fun x => A x * u x)
    (hη.continuous.mul hz) (hA.mul hu) hcη.mul_right hcA.mul_right (μ := μ)
  have hzbound : (∫ x, ‖z x‖^2 ∂μ) ≤ C * ∫ x, ‖f x‖^2 ∂μ := hbound f hf hcf c hc
  have hubound : (∫ x, ‖u x‖^2 ∂μ) ≤ ∫ x, ‖f x‖^2 ∂μ := mollifier_square_le μ c hc f hf.continuous hcf
  have he (x : E) := cutoff_convolution_commutator μ v (kernel E μ c) a b η f hk hck hη hf.continuous x
  simp_rw [he]
  change (∫ x, ‖η x * z x + A x * u x‖^2 ∂μ) ≤ _
  simp only [smul_eq_mul] at hz2 hu2
  calc
    _ ≤ 2 * ((∫ x, ‖η x * z x‖^2 ∂μ) + ∫ x, ‖A x * u x‖^2 ∂μ) := hsum
    _ ≤ 2 * (M^2 * (C * ∫ x, ‖f x‖^2 ∂μ) + N^2 * (∫ x, ‖f x‖^2 ∂μ)) :=
      mul_le_mul_of_nonneg_left (add_le_add
        (hz2.trans (mul_le_mul_of_nonneg_left hzbound (sq_nonneg M)))
        (hu2.trans (mul_le_mul_of_nonneg_left hubound (sq_nonneg N)))) (by norm_num)
    _ = _ := by ring

end TernaryPoly.CompactScalarMollifier
