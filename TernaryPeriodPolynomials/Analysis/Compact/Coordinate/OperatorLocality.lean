module

public import TernaryPeriodPolynomials.Analysis.Compact.Coordinate.LocalAdjoint

@[expose] public section


/-! The explicit coordinate formal adjoint depends only on the germ of its input field. -/
noncomputable section
namespace TernaryPoly.CompactCoordinateIntegration
open Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem transposeOrder_congr {g h : E → ℝ} {x : E} (he : g =ᶠ[𝓝 x] h)
    (v : E) (a b : E → ℝ) : transposeOrder v a b g x = transposeOrder v a b h x := by
  have hae : (fun y => a y * g y) =ᶠ[𝓝 x] (fun y => a y * h y) := by
    filter_upwards [he] with y hy
    rw [hy]
  simp only [transposeOrder, he.eq_of_nhds, hae.fderiv_eq]

variable {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]

omit [NormedSpace ℝ E] in
theorem metricDual_eventuallyEq (M : E → Matrix I I ℝ) {g h : I → E → ℝ} {x : E}
    (he : ∀ i, g i =ᶠ[𝓝 x] h i) (i : I) : metricDual M g i =ᶠ[𝓝 x] metricDual M h i := by
  have hall : ∀ᶠ y in 𝓝 x, ∀ l, g l y = h l y := Filter.eventually_all.mpr he
  filter_upwards [hall] with y hy
  unfold metricDual
  rw [show (fun l => g l y) = (fun l => h l y) from funext hy]

omit [Fintype I] in
theorem matrixTranspose_congr (v : K → E) (a b : J → I → K → E → ℝ)
    {g h : J → E → ℝ} {x : E} (he : ∀ j, g j =ᶠ[𝓝 x] h j) (i : I) :
    matrixTranspose v a b g i x = matrixTranspose v a b h i x := by
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  exact transposeOrder_congr (he j) (v k) (a j i k) (b j i k)

theorem weightedMatrixAdjoint_congr [DecidableEq I]
    (M : E → Matrix I I ℝ) (N : E → Matrix J J ℝ)
    (v : K → E) (a b : J → I → K → E → ℝ) {g h : J → E → ℝ}
    {x : E} (he : ∀ j, g j =ᶠ[𝓝 x] h j) (i : I) :
    weightedMatrixAdjoint M N v a b g i x = weightedMatrixAdjoint M N v a b h i x := by
  unfold weightedMatrixAdjoint metricDual Matrix.mulVec dotProduct
  apply Finset.sum_congr rfl
  intro l _
  congr 1
  exact matrixTranspose_congr v a b (fun j => metricDual_eventuallyEq N he j) l

end TernaryPoly.CompactCoordinateIntegration
