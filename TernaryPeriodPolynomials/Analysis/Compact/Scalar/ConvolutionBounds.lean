module

public import TernaryPeriodPolynomials.Analysis.Compact.Scalar.ConvolutionRegularity
public import TernaryPeriodPolynomials.Analysis.ScaledScalarKernelRegularity
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Measure.Haar.Unique

@[expose] public section

/-! Actual uniform mass bounds and common compact support for dilated scalar convolutions. -/
noncomputable section
namespace TernaryPoly.CompactCoordinateIntegration
open MeasureTheory ScaledScalarKernel Set
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

/-- A nonnegative kernel controls a convolution by its actual mass and the input bound. -/
theorem norm_scalarConvolution_le_mass (κ f : E → ℝ) (hk : Integrable κ μ)
    (hn : ∀ z, 0 ≤ κ z) (F : ℝ) (hF : ∀ y, ‖f y‖ ≤ F) (x : E) :
    ‖scalarConvolution μ κ f x‖ ≤ (∫ z, κ z ∂μ) * F := by
  rw [scalarConvolution_apply]
  have hi : Integrable (fun y => κ (x-y) * F) μ := (hk.comp_sub_left x).mul_const F
  calc
    _ ≤ ∫ y, κ (x-y) * F ∂μ := by
      apply norm_integral_le_of_norm_le hi
      exact Filter.Eventually.of_forall (fun y => by
        rw [norm_mul, Real.norm_of_nonneg (hn _), mul_comm]
        exact mul_le_mul_of_nonneg_left (hF y) (hn _))
    _ = _ := by rw [integral_mul_const, integral_sub_left_eq_self]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Dilations by at least one have a common support ball. -/
theorem support_dilate_subset_ball (κ : E → ℝ) (R c : ℝ) (hc : 1 ≤ c)
    (hk : Function.support κ ⊆ Metric.closedBall 0 R) :
    Function.support (dilate c κ) ⊆ Metric.closedBall 0 R := by
  intro x hx
  have hne : κ (c • x) ≠ 0 := (mul_ne_zero_iff.mp hx).2
  have h := hk hne
  simp only [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg (by linarith : 0 ≤ c)] at h ⊢
  exact (le_mul_of_one_le_left (norm_nonneg x) hc).trans h

omit [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure] in
/-- The convolution of a fixed compact input with a contracting kernel has a common closed ball. -/
theorem tsupport_scalarConvolution_dilate_subset (κ f : E → ℝ) (R S c : ℝ) (hc : 1 ≤ c)
    (hk : Function.support κ ⊆ Metric.closedBall 0 R)
    (hf : Function.support f ⊆ Metric.closedBall 0 S) :
    tsupport (scalarConvolution μ (dilate c κ) f) ⊆ Metric.closedBall 0 (S+R) := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  have hm := support_convolution_subset (ContinuousLinearMap.mul ℝ ℝ) hx
  rcases hm with ⟨y, hy, z, hz, rfl⟩
  have hy' := hf hy
  have hz' := support_dilate_subset_ball κ R c hc hk hz
  simp only [Metric.mem_closedBall, dist_zero_right] at hy' hz' ⊢
  exact (norm_add_le y z).trans (add_le_add hy' hz')

end TernaryPoly.CompactCoordinateIntegration
