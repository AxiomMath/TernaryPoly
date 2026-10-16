module

public import TernaryPeriodPolynomials.Analysis.Compact.Coordinate.LocalAdjoint

@[expose] public section


/-! Exact locality of the coordinate formal-adjoint expression. -/
noncomputable section
namespace TernaryPoly.CompactCoordinateIntegration
open Set
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Variable coefficients and differentiation cannot enlarge the closed support. -/
theorem tsupport_transposeOrder_subset (v : E) (a b g : E → ℝ) :
    tsupport (transposeOrder v a b g) ⊆ tsupport g := by
  apply closure_minimal _ (isClosed_tsupport g)
  intro x hx
  by_contra hn
  apply hx
  unfold transposeOrder
  rw [image_eq_zero_of_notMem_tsupport hn, mul_zero,
    fderiv_of_notMem_tsupport ℝ (fun h => hn (tsupport_mul_subset_right h))]
  simp only [zero_apply, sub_zero]

variable {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]

omit [NormedSpace ℝ E] in
theorem tsupport_sum_subset {ι : Type*} [Fintype ι] (f : ι → E → ℝ)
    {U : Set E} (hU : IsClosed U) (hf : ∀ i, tsupport (f i) ⊆ U) :
    tsupport (fun x => ∑ i, f i x) ⊆ U := by
  apply closure_minimal _ hU
  intro x hx
  by_contra hn
  apply hx
  exact Finset.sum_eq_zero (fun i _ => image_eq_zero_of_notMem_tsupport (fun hi => hn (hf i hi)))

omit [Fintype I] in
theorem tsupport_matrixTranspose_subset (v : K → E) (a b : J → I → K → E → ℝ)
    (g : J → E → ℝ) {U : Set E} (hU : IsClosed U) (hg : ∀ j, tsupport (g j) ⊆ U) (i : I) :
    tsupport (matrixTranspose v a b g i) ⊆ U :=
  tsupport_sum_subset _ hU (fun j => tsupport_sum_subset _ hU (fun k =>
    (tsupport_transposeOrder_subset (v k) (a j i k) (b j i k) (g j)).trans (hg j)))

/-- The inverse metric and transpose divergence preserve the original closed supporting set. -/
theorem tsupport_weightedMatrixAdjoint_subset [DecidableEq I]
    (M : E → Matrix I I ℝ) (N : E → Matrix J J ℝ)
    (v : K → E) (a b : J → I → K → E → ℝ) (g : J → E → ℝ)
    {U : Set E} (hU : IsClosed U) (hg : ∀ j, tsupport (g j) ⊆ U) (i : I) :
    tsupport (weightedMatrixAdjoint M N v a b g i) ⊆ U :=
  tsupport_metricDual_subset _ _ hU (fun l => tsupport_matrixTranspose_subset v a b
    (metricDual N g) hU (fun j => tsupport_metricDual_subset N g hU hg j) l) i

end TernaryPoly.CompactCoordinateIntegration
