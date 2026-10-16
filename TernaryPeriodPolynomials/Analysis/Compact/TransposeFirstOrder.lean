module

public import TernaryPeriodPolynomials.Analysis.Compact.Coordinate.FormalAdjoint
public import Mathlib.Analysis.Calculus.FDeriv.Add

@[expose] public section

/-! Actual transpose-divergence operators as ordinary first-order expressions. -/
noncomputable section
namespace TernaryPoly.CompactCoordinateIntegration
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The scalar transpose has the actual coefficient derivative in its zeroth-order term. -/
theorem transposeOrder_eq_firstOrder (v : E) (a b f : E → ℝ) (x : E)
    (ha : DifferentiableAt ℝ a x) (hf : DifferentiableAt ℝ f x) :
    transposeOrder v a b f x = firstOrder v (fun y => -a y)
      (fun y => b y - fderiv ℝ a y v) f x := by
  unfold transposeOrder firstOrder
  rw [fderiv_fun_mul ha hf]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

/-- Include the target metric coefficient before transposing, with every derivative retained. -/
theorem transposeOrder_product_firstOrder (v : E) (a b n f : E → ℝ) (x : E)
    (ha : DifferentiableAt ℝ a x) (hn : DifferentiableAt ℝ n x) (hf : DifferentiableAt ℝ f x) :
    transposeOrder v a b (fun y => n y * f y) x =
      firstOrder v (fun y => -a y * n y)
        (fun y => b y * n y - fderiv ℝ a y v * n y - a y * fderiv ℝ n y v) f x := by
  unfold transposeOrder firstOrder
  rw [fderiv_fun_mul ha (hn.fun_mul hf), fderiv_fun_mul hn hf]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

/-- Multiplication by the inverse source metric adds no derivative. -/
theorem mul_firstOrder (v : E) (m a b f : E → ℝ) (x : E) :
    m x * firstOrder v a b f x =
      firstOrder v (fun y => m y * a y) (fun y => m y * b y) f x := by
  unfold firstOrder
  ring

/-- The actual transpose-divergence is linear over finite sums of differentiable inputs. -/
theorem transposeOrder_finsetSum {I : Type*} (s : Finset I) (v : E) (a b : E → ℝ)
    (f : I → E → ℝ) (x : E) (ha : DifferentiableAt ℝ a x)
    (hf : ∀ i ∈ s, DifferentiableAt ℝ (f i) x) :
    transposeOrder v a b (fun y => ∑ i ∈ s, f i y) x = ∑ i ∈ s, transposeOrder v a b (f i) x := by
  have he : (fun y => a y * ∑ i ∈ s, f i y) = fun y => ∑ i ∈ s, a y * f i y := by
    funext y
    exact Finset.mul_sum _ _ _
  unfold transposeOrder
  rw [he, fderiv_fun_sum (fun i hi => ha.fun_mul (hf i hi))]
  simp only [sum_apply, Finset.mul_sum, Finset.sum_sub_distrib]

end TernaryPoly.CompactCoordinateIntegration
