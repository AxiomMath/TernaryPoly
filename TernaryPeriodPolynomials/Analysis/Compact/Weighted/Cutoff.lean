module

public import TernaryPeriodPolynomials.Analysis.Compact.Coordinate.Cutoff

@[expose] public section


/-! Exact cutoff commutators for the genuine inverse-Gram transpose divergence. -/
noncomputable section
namespace TernaryPoly.CompactCoordinateIntegration
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {I J K : Type*} [Fintype I] [Fintype J] [Fintype K] [DecidableEq I]

/-- The inverse source Gram times the target-metric transpose of the differential symbol. -/
def weightedSymbolTranspose (M : E → Matrix I I ℝ) (N : E → Matrix J J ℝ)
    (v : K → E) (a : J → I → K → E → ℝ) (c : E → ℝ)
    (g : J → E → ℝ) : I → E → ℝ :=
  metricDual (fun x => (M x)⁻¹) (matrixSymbolTranspose v a c (metricDual N g))

/-- Differentiability of every entry of the genuine target metric dual. -/
theorem differentiableAt_metricDual (N : E → Matrix J J ℝ) (g : J → E → ℝ) {x : E}
    (hN : ∀ j l, DifferentiableAt ℝ (fun y => N y j l) x)
    (hg : ∀ j, DifferentiableAt ℝ (g j) x) (j : J) :
    DifferentiableAt ℝ (metricDual N g j) x := by
  unfold metricDual Matrix.mulVec dotProduct
  apply DifferentiableAt.fun_sum
  intro l _
  exact (hN j l).fun_mul (hg l)

/-- The actual weighted adjoint's cutoff commutator is a zeroth-order symbol expression. -/
theorem weightedMatrixAdjoint_cutoff (M : E → Matrix I I ℝ) (N : E → Matrix J J ℝ)
    (v : K → E) (a b : J → I → K → E → ℝ) (c : E → ℝ) (g : J → E → ℝ) {x : E}
    (ha : ∀ j i k, DifferentiableAt ℝ (a j i k) x)
    (hN : ∀ j l, DifferentiableAt ℝ (fun y => N y j l) x)
    (hc : DifferentiableAt ℝ c x) (hg : ∀ j, DifferentiableAt ℝ (g j) x) (i : I) :
    weightedMatrixAdjoint M N v a b (fun j y => c y * g j y) i x =
      c x * weightedMatrixAdjoint M N v a b g i x - weightedSymbolTranspose M N v a c g i x := by
  have he : metricDual N (fun j y => c y * g j y) = fun j y => c y * metricDual N g j y := by
    funext j y
    exact metricDual_cutoff N c g j y
  unfold weightedMatrixAdjoint
  rw [he]
  change (∑ l, (M x)⁻¹ i l * matrixTranspose v a b (fun j y => c y * metricDual N g j y) l x) = _
  simp_rw [matrixTranspose_cutoff v a b c (metricDual N g) ha hc
    (differentiableAt_metricDual N g hN hg)]
  simp only [weightedSymbolTranspose, metricDual, Matrix.mulVec, dotProduct,
    mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  ring

end TernaryPoly.CompactCoordinateIntegration
