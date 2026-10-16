module

public import TernaryPeriodPolynomials.DifferentialForm.Connection.Divergence

@[expose] public section


/-! Locality of actual weighted divergence outside the genuine projected support. -/
noncomputable section
namespace TernaryPoly.PolynomialFormConnection
open SymmetricSpaceCharts SymmetricSpaceRiemannian SmoothCoveringDeRham Set Filter
open scoped Topology

theorem vector_eventuallyEq_zero_of_notMem_projected_support (V : Coordinates → Coordinates)
    (x : Coordinates) (hx : x ∈ positiveCoordinates)
    (hs : coordinateProjection x ∉ closure (coordinateProjection '' Function.support V)) :
    V =ᶠ[𝓝 x] 0 := by
  have hp : ContinuousAt coordinateProjection x := coordinateProjection_continuousOn.continuousAt
    (isOpen_positiveCoordinates.mem_nhds hx)
  have hnear : ∀ᶠ y in 𝓝 x, coordinateProjection y ∉ closure (coordinateProjection '' Function.support V) :=
    hp.eventually (isClosed_closure.isOpen_compl.mem_nhds hs)
  filter_upwards [hnear] with y hy
  by_contra hn
  exact hy (subset_closure ⟨y, hn, rfl⟩)

theorem weightedDivergence_eq_zero_of_eventuallyEq_zero (V : Coordinates → Coordinates)
    (x : Coordinates) (hV : V =ᶠ[𝓝 x] 0) : weightedDivergence V x = 0 := by
  have hi (i : Fin 5) : (fun y => coordinateDensity y * V y i) =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
    filter_upwards [hV] with y hy
    simp only [hy, Pi.zero_apply, mul_zero]
  have hd (i : Fin 5) : fderiv ℝ (fun y => coordinateDensity y * V y i) x = 0 :=
    (hi i).fderiv_eq.trans (fderiv_const_apply 0)
  simp only [weightedDivergence, hd, _root_.zero_apply, Finset.sum_const_zero, mul_zero]

theorem weightedDivergence_eq_zero_of_notMem_projected_support (V : Coordinates → Coordinates)
    (x : Coordinates) (hx : x ∈ positiveCoordinates)
    (hs : coordinateProjection x ∉ closure (coordinateProjection '' Function.support V)) :
    weightedDivergence V x = 0 :=
  weightedDivergence_eq_zero_of_eventuallyEq_zero V x
    (vector_eventuallyEq_zero_of_notMem_projected_support V x hx hs)

end TernaryPoly.PolynomialFormConnection
