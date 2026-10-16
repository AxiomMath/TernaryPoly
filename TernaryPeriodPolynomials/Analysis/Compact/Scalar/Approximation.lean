module

public import TernaryPeriodPolynomials.Analysis.Compact.Scalar.ConvolutionRegularity
public import TernaryPeriodPolynomials.Analysis.ScaledScalarKernelRegularity
public import Mathlib.MeasureTheory.Integral.PeakFunction
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Extend
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

@[expose] public section


/-! Genuine pointwise approximation by the actual mass-preserving convolution family. -/
noncomputable section
namespace TernaryPoly.CompactCoordinateIntegration
open MeasureTheory Filter
open ScaledScalarKernel
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

/-- Every nonnegative normalized compact kernel gives actual convergence at continuous points. -/
theorem scalarConvolution_dilate_tendsto (κ f : E → ℝ)
    (hκ : ∀ x, 0 ≤ κ x) (hmass : ∫ x, κ x ∂μ = 1) (hcκ : HasCompactSupport κ)
    (hf : Integrable f μ) (x : E) (hfx : ContinuousAt f x) :
    Tendsto (fun c : ℝ => scalarConvolution μ (dilate c κ) f x) atTop (nhds (f x)) := by
  have hdecay : Tendsto (fun z : E => ‖z‖ ^ Module.finrank ℝ E * κ z)
      (Bornology.cobounded E) (nhds 0) := by
    have h := (hcκ.mul_left (f := fun z => ‖z‖ ^ Module.finrank ℝ E)).is_zero_at_infty
    change Tendsto (fun z : E => ‖z‖ ^ Module.finrank ℝ E * κ z) (cocompact E) (nhds 0) at h
    rwa [Metric.cobounded_eq_cocompact]
  have h := tendsto_integral_comp_smul_smul_of_integrable' hκ hmass hdecay hf hfx
  simpa only [scalarConvolution_apply, dilate, smul_eq_mul, mul_comm] using h

theorem scalarConvolution_comm (κ f : E → ℝ) :
    scalarConvolution μ κ f = scalarConvolution μ f κ := by
  have hL : (ContinuousLinearMap.mul ℝ ℝ).flip = ContinuousLinearMap.mul ℝ ℝ := by
    ext
    exact mul_comm _ _
  have h := convolution_flip (μ := μ) (L := ContinuousLinearMap.mul ℝ ℝ) (f := f) (g := κ)
  rw [hL] at h
  exact h.symm

/-- For compact C1 inputs one may differentiate the input instead of the scaled kernel. -/
theorem fderiv_scalarConvolution_eq_input (κ f : E → ℝ)
    (hκ : Continuous κ) (hcκ : HasCompactSupport κ)
    (hf : ContDiff ℝ 1 f) (hcf : HasCompactSupport f) (x v : E) :
    fderiv ℝ (scalarConvolution μ κ f) x v =
      scalarConvolution μ κ (fun y => fderiv ℝ f y v) x := by
  have he := scalarConvolution_comm μ κ f
  rw [he, fderiv_scalarConvolution μ f κ hf hcf hκ hcκ]
  change scalarConvolution μ (fun y => fderiv ℝ f y v) κ x = _
  exact congrFun (scalarConvolution_comm μ (fun y => fderiv ℝ f y v) κ) x

end TernaryPoly.CompactCoordinateIntegration
