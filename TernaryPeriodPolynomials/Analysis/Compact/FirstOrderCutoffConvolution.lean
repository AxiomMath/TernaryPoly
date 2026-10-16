module

public import TernaryPeriodPolynomials.Analysis.Compact.FirstOrderConvolutionBound

@[expose] public section


/-! Fixed-scale derivatives of cutoff convolution retain all derivative-of-cutoff terms. -/
noncomputable section
namespace TernaryPoly.CompactCoordinateIntegration
open MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem firstOrder_mul (v : E) (a b η f : E → ℝ) (x : E)
    (hη : DifferentiableAt ℝ η x) (hf : DifferentiableAt ℝ f x) :
    firstOrder v a b (fun y => η y * f y) x =
      firstOrder v (fun y => a y * η y) (fun y => a y * fderiv ℝ η y v + b y * η y) f x := by
  unfold firstOrder
  rw [fderiv_fun_mul hη hf]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

theorem exists_firstOrder_cutoff_convolution_bound (v : E) (κ a b η : E → ℝ)
    (hκ : ContDiff ℝ 1 κ) (hcκ : HasCompactSupport κ) (ha : Continuous a) (hb : Continuous b)
    (hη : ContDiff ℝ 1 η) (hcη : HasCompactSupport η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : E → ℝ, Continuous f → HasCompactSupport f →
      ∫ x, ‖firstOrder v a b (fun y => η y * scalarConvolution μ κ f y) x‖^2 ∂μ ≤
        C * ∫ x, ‖f x‖^2 ∂μ := by
  let A := fun x => a x * η x
  let B := fun x => a x * fderiv ℝ η x v + b x * η x
  have hB : Continuous B :=
    (ha.mul ((hη.continuous_fderiv one_ne_zero).clm_apply continuous_const)).add (hb.mul hη.continuous)
  obtain ⟨C,hC,hbound⟩ := exists_firstOrder_convolution_bound μ v κ A B hκ hcκ
    (ha.mul hη.continuous) hB hcη.mul_left ((hcη.fderiv_apply ℝ v).mul_left.add hcη.mul_left)
  refine ⟨C,hC,fun f hf hcf => ?_⟩
  have he (x : E) := firstOrder_mul v a b η (scalarConvolution μ κ f) x
    (hη.differentiable one_ne_zero x)
    ((contDiff_scalarConvolution μ κ f hκ hcκ hf).differentiable one_ne_zero x)
  simpa only [he] using hbound f hf hcf

end TernaryPoly.CompactCoordinateIntegration
