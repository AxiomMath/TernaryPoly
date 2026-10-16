module

public import TernaryPeriodPolynomials.Analysis.WeightedIntegralSquare
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section


/-! The L2 Schur bound for nonnegative dominating kernels, in actual integral form. -/
namespace TernaryPoly.KernelSquareBound
open MeasureTheory
variable {X Y F : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Row and column mass bounds control the square integral of a genuine kernel operator. -/
theorem integral_norm_square_le (K : X → Y → ℝ) (f : Y → F)
    (hK : ∀ x y, 0 ≤ K x y) (A B : ℝ) (hA : 0 ≤ A)
    (hrow : ∀ x, ∫ y, K x y ∂ν ≤ A) (hcol : ∀ y, ∫ x, K x y ∂μ ≤ B)
    (h0 : ∀ x, Integrable (K x) ν)
    (h1 : ∀ x, Integrable (fun y => K x y * ‖f y‖) ν)
    (h2 : ∀ x, Integrable (fun y => K x y * ‖f y‖ ^ 2) ν)
    (hprod : Integrable (fun p : X × Y => K p.1 p.2 * ‖f p.2‖ ^ 2) (μ.prod ν))
    (hf : Integrable (fun y => ‖f y‖ ^ 2) ν)
    (hout : Integrable (fun x => ‖∫ y, K x y • f y ∂ν‖ ^ 2) μ) :
    ∫ x, ‖∫ y, K x y • f y ∂ν‖ ^ 2 ∂μ ≤ (A * B) * ∫ y, ‖f y‖ ^ 2 ∂ν := by
  have hpoint (x : X) : ‖∫ y, K x y • f y ∂ν‖ ^ 2 ≤
      A * ∫ y, K x y * ‖f y‖ ^ 2 ∂ν :=
    (WeightedIntegralSquare.norm_integral_smul_square_le (K x) f (hK x) (h0 x) (h1 x) (h2 x)).trans
      (mul_le_mul_of_nonneg_right (hrow x) (integral_nonneg (fun y => mul_nonneg (hK x y) (sq_nonneg _))))
  have hcolint : (∫ y, ∫ x, K x y * ‖f y‖ ^ 2 ∂μ ∂ν) ≤ B * ∫ y, ‖f y‖ ^ 2 ∂ν := by
    rw [← integral_const_mul]
    apply integral_mono hprod.integral_prod_right (hf.const_mul B)
    intro y
    dsimp only
    rw [integral_mul_const]
    exact mul_le_mul_of_nonneg_right (hcol y) (sq_nonneg _)
  calc
    _ ≤ ∫ x, A * ∫ y, K x y * ‖f y‖ ^ 2 ∂ν ∂μ :=
      integral_mono hout (hprod.integral_prod_left.const_mul A) hpoint
    _ = A * ∫ y, ∫ x, K x y * ‖f y‖ ^ 2 ∂μ ∂ν := by
      rw [integral_const_mul, integral_integral_swap hprod]
    _ ≤ A * (B * ∫ y, ‖f y‖ ^ 2 ∂ν) := mul_le_mul_of_nonneg_left hcolint hA
    _ = _ := by ring

end TernaryPoly.KernelSquareBound
