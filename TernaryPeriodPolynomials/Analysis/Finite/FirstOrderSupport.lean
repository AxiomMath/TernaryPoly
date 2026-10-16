module

public import TernaryPeriodPolynomials.Analysis.Compact.Coordinate.OperatorSupport

@[expose] public section


/-! Scalar and finite first-order expressions preserve the exact closed input support. -/
noncomputable section
namespace TernaryPoly.CompactCoordinateIntegration
open Set
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem tsupport_firstOrder_subset (v : E) (a b f : E → ℝ) :
    tsupport (firstOrder v a b f) ⊆ tsupport f := by
  apply closure_minimal _ (isClosed_tsupport f)
  intro x hx
  by_contra hn
  apply hx
  unfold firstOrder
  rw [image_eq_zero_of_notMem_tsupport hn, fderiv_of_notMem_tsupport ℝ hn]
  simp only [zero_apply, mul_zero, add_zero]

theorem tsupport_matrixFirstOrder_subset {I J K : Type*} [Fintype I] [Fintype K]
    (v : K → E) (a b : J → I → K → E → ℝ) (f : I → E → ℝ)
    {T : Set E} (hT : IsClosed T) (hf : ∀ i, tsupport (f i) ⊆ T) (j : J) :
    tsupport (matrixFirstOrder v a b f j) ⊆ T :=
  tsupport_sum_subset _ hT (fun i => tsupport_sum_subset _ hT (fun d =>
    (tsupport_firstOrder_subset (v d) (a j i d) (b j i d) (f i)).trans (hf i)))

end TernaryPoly.CompactCoordinateIntegration
