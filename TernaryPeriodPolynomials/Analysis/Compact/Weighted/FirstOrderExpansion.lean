module

public import TernaryPeriodPolynomials.Analysis.Compact.Weighted.MatrixAdjoint
public import TernaryPeriodPolynomials.Analysis.Compact.TransposeFirstOrder

@[expose] public section


/-! Literal inverse-Gram transpose divergence expanded into scalar first-order coefficients. -/
noncomputable section
namespace TernaryPoly.CompactCoordinateIntegration
variable {E I J K : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Fintype I] [Fintype J] [Fintype K] [DecidableEq I]

/-- Actual first-order coefficient of the weighted adjoint for one source/target summand. -/
def weightedFirstCoefficient (M : E → Matrix I I ℝ) (N : E → Matrix J J ℝ)
    (a : J → I → K → E → ℝ) (i : I) (t : J) (l : I) (j : J) (k : K) (x : E) : ℝ :=
  (M x)⁻¹ i l * (-a j l k x * N x j t)

/-- Actual zeroth-order coefficient, including both differentiated coefficient and target metric. -/
def weightedZeroCoefficient (M : E → Matrix I I ℝ) (N : E → Matrix J J ℝ)
    (v : K → E) (a b : J → I → K → E → ℝ)
    (i : I) (t : J) (l : I) (j : J) (k : K) (x : E) : ℝ :=
  (M x)⁻¹ i l * (b j l k x * N x j t - fderiv ℝ (a j l k) x (v k) * N x j t -
    a j l k x * fderiv ℝ (fun y => N y j t) x (v k))

/-- Every actual weighted adjoint is a finite sum of explicit ordinary first-order operators.
No invertibility or formal-adjoint hypothesis is required for this identity of literal expressions. -/
theorem weightedMatrixAdjoint_firstOrder_expansion
    (M : E → Matrix I I ℝ) (N : E → Matrix J J ℝ)
    (v : K → E) (a b : J → I → K → E → ℝ) (g : J → E → ℝ) (i : I) (x : E)
    (ha : ∀ j l k, DifferentiableAt ℝ (a j l k) x)
    (hN : ∀ j t, DifferentiableAt ℝ (fun y => N y j t) x)
    (hg : ∀ t, DifferentiableAt ℝ (g t) x) :
    weightedMatrixAdjoint M N v a b g i x =
      ∑ l, ∑ j, ∑ k, ∑ t, firstOrder (v k) (weightedFirstCoefficient M N a i t l j k)
        (weightedZeroCoefficient M N v a b i t l j k) (g t) x := by
  change (∑ l, (M x)⁻¹ i l * ∑ j, ∑ k,
    transposeOrder (v k) (a j l k) (b j l k) (metricDual N g j) x) = _
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  have he : metricDual N g j = fun y => ∑ t, N y j t * g t y := rfl
  rw [he]
  rw [transposeOrder_finsetSum Finset.univ (v k) (a j l k) (b j l k)
    (fun t y => N y j t * g t y) x (ha j l k) (fun t _ => (hN j t).fun_mul (hg t)), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  rw [transposeOrder_product_firstOrder (v k) (a j l k) (b j l k) (fun y => N y j t) (g t) x
    (ha j l k) (hN j t) (hg t)]
  exact mul_firstOrder (v k) (fun y => (M y)⁻¹ i l) _ _ (g t) x

end TernaryPoly.CompactCoordinateIntegration
