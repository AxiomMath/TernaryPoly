module

public import TernaryPeriodPolynomials.Analysis.Compact.Scalar.ConvolutionRegularity
public import TernaryPeriodPolynomials.Analysis.Compact.Scalar.Mollifier
public import TernaryPeriodPolynomials.Analysis.DominatedKernelSquareBound
public import Mathlib.MeasureTheory.Group.Integral

@[expose] public section


/-! The signed-kernel L2 bound needed for fixed-scale derivatives of actual regularizers. -/
noncomputable section
namespace TernaryPoly.CompactCoordinateIntegration
open MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

theorem scalarConvolution_signed_square_le (κ f : E → ℝ)
    (hκ : ContDiff ℝ 0 κ) (hcκ : HasCompactSupport κ)
    (hf : Continuous f) (hcf : HasCompactSupport f) :
    ∫ x, ‖scalarConvolution μ κ f x‖ ^ 2 ∂μ ≤
      (∫ z, ‖κ z‖ ∂μ)^2 * ∫ y, ‖f y‖ ^ 2 ∂μ := by
  have hki := hκ.continuous.norm.integrable_of_hasCompactSupport hcκ.norm (μ := μ)
  have hgi : Integrable (fun y => ‖f y‖ ^ 2) μ :=
    (hf.norm.pow 2).integrable_of_hasCompactSupport (by
      simpa only [pow_two, Pi.mul_apply, Pi.sub_apply, Function.comp_def, id_eq] using hcf.norm.mul_right (f' := fun y => ‖f y‖))
  have h0 (x : E) : Integrable (fun y => ‖κ (x-y)‖) μ := hki.comp_sub_left x
  have h1 (x : E) : Integrable (fun y => ‖κ (x-y)‖ * ‖f y‖) μ :=
    ((hκ.continuous.norm.comp (continuous_const.sub continuous_id)).mul hf.norm).integrable_of_hasCompactSupport
      hcf.norm.mul_left
  have h2 (x : E) : Integrable (fun y => ‖κ (x-y)‖ * ‖f y‖ ^ 2) μ :=
    ((hκ.continuous.norm.comp (continuous_const.sub continuous_id)).mul (hf.norm.pow 2)).integrable_of_hasCompactSupport
      (by simpa only [pow_two, Pi.mul_apply, Pi.sub_apply, Function.comp_def, id_eq] using
        (hcf.norm.mul_right (f' := fun y => ‖f y‖)).mul_left (f := fun y => ‖κ (x-y)‖))
  have hp : Integrable (fun p : E × E => ‖κ (p.1-p.2)‖ * ‖f p.2‖ ^ 2) (μ.prod μ) := by
    simpa only [ContinuousLinearMap.mul_apply', mul_comm] using
      hgi.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) hki
  have hconv := contDiff_scalarConvolution μ κ f hκ hcκ hf
  have hcconv := compact_scalarConvolution μ κ f hcκ hcf
  have hout : Integrable (fun x => ‖scalarConvolution μ κ f x‖ ^ 2) μ :=
    (hconv.continuous.norm.pow 2).integrable_of_hasCompactSupport (by
      simpa only [pow_two, Pi.mul_apply, Pi.sub_apply, Function.comp_def, id_eq] using hcconv.norm.mul_right
        (f' := fun x => ‖scalarConvolution μ κ f x‖))
  have hT (x : E) : ‖scalarConvolution μ κ f x‖ ≤ ∫ y, ‖κ (x-y)‖ * ‖f y‖ ∂μ := by
    rw [scalarConvolution_apply]
    apply norm_integral_le_of_norm_le (h1 x)
    exact Filter.Eventually.of_forall (fun y => by
      rw [norm_mul, mul_comm])
  have h := KernelSquareBound.integral_norm_square_le_of_dominated
    (fun x y => ‖κ (x-y)‖) (fun y => ‖f y‖) (scalarConvolution μ κ f)
    (fun x y => norm_nonneg (κ (x-y))) (fun y => norm_nonneg (f y))
    (∫ z, ‖κ z‖ ∂μ) (∫ z, ‖κ z‖ ∂μ) (integral_nonneg (fun z => norm_nonneg (κ z)))
    (fun x => (integral_sub_left_eq_self (fun z => ‖κ z‖) μ x).le)
    (fun y => (integral_sub_right_eq_self (fun z => ‖κ z‖) y).le) h0 h1 h2 hp hgi hout hT
  simpa only [pow_two] using h

end TernaryPoly.CompactCoordinateIntegration
