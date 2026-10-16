module

public import TernaryPeriodPolynomials.Analysis.KernelSquareBound

@[expose] public section


/-! The Schur bound for an actual possibly signed operator dominated by a nonnegative kernel. -/
namespace TernaryPoly.KernelSquareBound
open MeasureTheory
variable {X Y F : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν]
  [NormedAddCommGroup F]

/-- A pointwise dominating kernel suffices; the operator itself need not be positive. -/
theorem integral_norm_square_le_of_dominated (K : X → Y → ℝ) (g : Y → ℝ)
    (T : X → F) (hK : ∀ x y, 0 ≤ K x y) (hg : ∀ y, 0 ≤ g y)
    (A B : ℝ) (hA : 0 ≤ A)
    (hrow : ∀ x, ∫ y, K x y ∂ν ≤ A) (hcol : ∀ y, ∫ x, K x y ∂μ ≤ B)
    (h0 : ∀ x, Integrable (K x) ν)
    (h1 : ∀ x, Integrable (fun y => K x y * g y) ν)
    (h2 : ∀ x, Integrable (fun y => K x y * g y ^ 2) ν)
    (hprod : Integrable (fun p : X × Y => K p.1 p.2 * g p.2 ^ 2) (μ.prod ν))
    (hgin : Integrable (fun y => g y ^ 2) ν)
    (hout : Integrable (fun x => ‖T x‖ ^ 2) μ)
    (hT : ∀ x, ‖T x‖ ≤ ∫ y, K x y * g y ∂ν) :
    ∫ x, ‖T x‖ ^ 2 ∂μ ≤ (A * B) * ∫ y, g y ^ 2 ∂ν := by
  have hpoint (x : X) : ‖T x‖ ^ 2 ≤ A * ∫ y, K x y * g y ^ 2 ∂ν := by
    have hn := norm_nonneg (T x)
    have ht := hT x
    have hcs := WeightedIntegralSquare.integral_square_le (K x) g (hK x) (h0 x) (h1 x) (h2 x)
    have hi : 0 ≤ ∫ y, K x y * g y ∂ν := integral_nonneg (fun y => mul_nonneg (hK x y) (hg y))
    have hsq : ‖T x‖ ^ 2 ≤ (∫ y, K x y * g y ∂ν) ^ 2 := by nlinarith
    exact (hsq.trans hcs).trans (mul_le_mul_of_nonneg_right (hrow x)
      (integral_nonneg (fun y => mul_nonneg (hK x y) (sq_nonneg _))))
  have hcolint : (∫ y, ∫ x, K x y * g y ^ 2 ∂μ ∂ν) ≤ B * ∫ y, g y ^ 2 ∂ν := by
    rw [← integral_const_mul]
    apply integral_mono hprod.integral_prod_right (hgin.const_mul B)
    intro y
    dsimp only
    rw [integral_mul_const]
    exact mul_le_mul_of_nonneg_right (hcol y) (sq_nonneg _)
  calc
    _ ≤ ∫ x, A * ∫ y, K x y * g y ^ 2 ∂ν ∂μ :=
      integral_mono hout (hprod.integral_prod_left.const_mul A) hpoint
    _ = A * ∫ y, ∫ x, K x y * g y ^ 2 ∂μ ∂ν := by
      rw [integral_const_mul, integral_integral_swap hprod]
    _ ≤ A * (B * ∫ y, g y ^ 2 ∂ν) := mul_le_mul_of_nonneg_left hcolint hA
    _ = _ := by ring

end TernaryPoly.KernelSquareBound
