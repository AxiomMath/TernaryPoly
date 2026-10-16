module

public import TernaryPeriodPolynomials.Analysis.Compact.CutoffCommutatorIdentity
public import TernaryPeriodPolynomials.Analysis.Compact.Scalar.ConvolutionLinear

@[expose] public section


/-! Exact localization at both input and output retains both cutoff commutators. -/
noncomputable section
namespace TernaryPoly.CompactCoordinateIntegration
open MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem firstOrder_cutoff (v : E) (a b χ f : E → ℝ) (x : E)
    (hχ : DifferentiableAt ℝ χ x) (hf : DifferentiableAt ℝ f x) :
    firstOrder v a b (fun y => χ y * f y) x =
      χ x * firstOrder v a b f x + (a x * fderiv ℝ χ x v) * f x := by
  rw [firstOrder_mul v a b χ f x hχ hf]
  simp only [firstOrder]
  ring

omit [FiniteDimensional ℝ E] in
theorem double_cutoff_convolution_commutator (v : E) (κ a b χ η f : E → ℝ)
    (hκ : Continuous κ) (ha : Continuous a) (hb : Continuous b)
    (hχ : ContDiff ℝ 1 χ) (hcχ : HasCompactSupport χ) (hf : ContDiff ℝ 1 f) (x : E) :
    firstOrder v a b (fun y => η y * scalarConvolution μ κ (fun z => χ z * f z) y) x -
      η x * scalarConvolution μ κ (fun z => χ z * firstOrder v a b f z) x =
      (firstOrder v a b (fun y => η y * scalarConvolution μ κ (fun z => χ z * f z) y) x -
        η x * scalarConvolution μ κ (firstOrder v a b (fun z => χ z * f z)) x) +
      η x * scalarConvolution μ κ (fun z => (a z * fderiv ℝ χ z v) * f z) x := by
  have he : firstOrder v a b (fun z => χ z * f z) =
      (fun z => χ z * firstOrder v a b f z) + (fun z => (a z * fderiv ℝ χ z v) * f z) :=
    funext (fun z => firstOrder_cutoff v a b χ f z (hχ.differentiable one_ne_zero z) (hf.differentiable one_ne_zero z))
  have hec := scalarConvolution_add μ κ
    (fun z => χ z * firstOrder v a b f z) (fun z => (a z * fderiv ℝ χ z v) * f z)
    hκ (hχ.continuous.mul (continuous_firstOrder v ha hb hf))
    ((ha.mul ((hχ.continuous_fderiv one_ne_zero).clm_apply continuous_const)).mul hf.continuous)
    hcχ.mul_right ((hcχ.fderiv_apply ℝ v).mul_left.mul_right)
  rw [he, hec]
  simp only [Pi.add_apply]
  ring

end TernaryPoly.CompactCoordinateIntegration
