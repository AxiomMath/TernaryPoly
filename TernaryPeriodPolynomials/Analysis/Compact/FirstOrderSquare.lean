module

public import TernaryPeriodPolynomials.Analysis.Compact.Coordinate.FormalAdjoint
public import TernaryPeriodPolynomials.Analysis.Compact.SquareIntegral
public import Mathlib.Tactic.Linarith

@[expose] public section

/-! Actual first-order L2 estimates in scalar coordinates. -/
noncomputable section
namespace TernaryPoly.CompactCoordinateIntegration
open MeasureTheory CompactSquareIntegral
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

omit [FiniteDimensional ℝ E] in
theorem integral_firstOrder_square_le (v : E) (a b f : E → ℝ)
    (ha : Continuous a) (hb : Continuous b) (hf : ContDiff ℝ 1 f) (hcf : HasCompactSupport f)
    (A B : ℝ) (haA : ∀ x, ‖a x‖ ≤ A) (hbB : ∀ x, ‖b x‖ ≤ B) :
    ∫ x, ‖firstOrder v a b f x‖^2 ∂μ ≤
      2 * (A^2 * (∫ x, ‖fderiv ℝ f x v‖^2 ∂μ) + B^2 * (∫ x, ‖f x‖^2 ∂μ)) := by
  have hd := (hf.continuous_fderiv one_ne_zero).clm_apply (continuous_const (y := v))
  have hdi := integrable_norm_square (fun x => fderiv ℝ f x v) hd (hcf.fderiv_apply ℝ v) (μ := μ)
  have hfi := integrable_norm_square f hf.continuous hcf (μ := μ)
  have hpi := integrable_norm_square (firstOrder v a b f)
    (continuous_firstOrder v ha hb hf) (compact_firstOrder v a b hcf) (μ := μ)
  have hp (x : E) : ‖firstOrder v a b f x‖^2 ≤
      2 * (A^2 * ‖fderiv ℝ f x v‖^2 + B^2 * ‖f x‖^2) := by
    have ha2 : a x ^ 2 ≤ A^2 := by
      simpa only [Real.norm_eq_abs, sq_abs] using pow_le_pow_left₀ (norm_nonneg (a x)) (haA x) 2
    have hb2 : b x ^ 2 ≤ B^2 := by
      simpa only [Real.norm_eq_abs, sq_abs] using pow_le_pow_left₀ (norm_nonneg (b x)) (hbB x) 2
    have h1 := mul_le_mul_of_nonneg_right ha2 (sq_nonneg (fderiv ℝ f x v))
    have h2 := mul_le_mul_of_nonneg_right hb2 (sq_nonneg (f x))
    have h3 : (a x * fderiv ℝ f x v + b x * f x)^2 ≤
        2 * ((a x * fderiv ℝ f x v)^2 + (b x * f x)^2) := add_sq_le
    simp only [firstOrder, Real.norm_eq_abs, sq_abs]
    nlinarith
  have h := integral_mono hpi ((hdi.const_mul _).add (hfi.const_mul _) |>.const_mul 2) hp
  simpa only [Pi.add_apply, integral_const_mul, integral_add (hdi.const_mul _) (hfi.const_mul _)] using h

end TernaryPoly.CompactCoordinateIntegration
