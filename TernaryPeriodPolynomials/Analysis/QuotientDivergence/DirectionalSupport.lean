module

public import TernaryPeriodPolynomials.Analysis.QuotientDivergence.ChartVectorCutoff

@[expose] public section


/-! Exact support control for the genuine directional scalar on the quotient. -/
noncomputable section
namespace TernaryPoly.QuotientScalarDescent
open SymmetricSpacePositive SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpaceQuotientManifold
  PolynomialCoefficientBundle SmoothCoveringDeRham SmoothDeRhamGluing PolynomialFormConnection Set Filter
open scoped ContDiff Manifold Topology

theorem coordinateProjection_chosen (q : OrbitSpace) :
    coordinateProjection (coordinateChart (chosenLift q)) = q := by
  rw [coordinateProjection, coordinateChart.left_inv (by simp), chosenLift_projection]

theorem coordinateDirectional_zero_of_notMem_tsupport (φ : OrbitSpace → ℝ)
    (V : Coordinates → Coordinates) (x : Coordinates) (hx : x ∈ positiveCoordinates)
    (hφ : coordinateProjection x ∉ tsupport φ) : coordinateDirectional φ V x = 0 := by
  have hc := coordinateProjection_continuousOn.continuousAt (isOpen_positiveCoordinates.mem_nhds hx)
  have he : liftScalar φ =ᶠ[𝓝 x] 0 := (notMem_tsupport_iff_eventuallyEq.mp hφ).comp_tendsto hc
  have hz : fderiv ℝ (liftScalar φ) x = 0 := by
    rw [he.fderiv_eq]
    exact fderiv_const_apply 0
  exact congrArg (fun L : Coordinates →L[ℝ] ℝ => L (V x)) hz

theorem directional_support_scalar (φ : OrbitSpace → ℝ) (V : Coordinates → Coordinates) :
    Function.support (directional φ V) ⊆ tsupport φ := by
  intro q hq
  by_contra h
  apply hq
  exact coordinateDirectional_zero_of_notMem_tsupport φ V _ (extract_mem _)
    (by simpa only [coordinateProjection_chosen] using h)

theorem directional_support_vector (φ : OrbitSpace → ℝ) (V : Coordinates → Coordinates) :
    Function.support (directional φ V) ⊆ projectedVectorSupport V := by
  intro q hq
  have hv : V (coordinateChart (chosenLift q)) ≠ 0 := by
    intro h
    apply hq
    change fderiv ℝ (liftScalar φ) (coordinateChart (chosenLift q)) (V (coordinateChart (chosenLift q))) = 0
    rw [h,map_zero]
  have h : coordinateProjection (coordinateChart (chosenLift q)) ∈ projectedVectorSupport V :=
    subset_closure (mem_image_of_mem coordinateProjection (show coordinateChart (chosenLift q) ∈ Function.support V from hv))
  simpa only [coordinateProjection_chosen] using h

theorem directional_compact (φ : OrbitSpace → ℝ) (V : Coordinates → Coordinates)
    (hK : IsCompact (projectedVectorSupport V)) : HasCompactSupport (directional φ V) :=
  hK.of_isClosed_subset (isClosed_tsupport _) (closure_minimal (directional_support_vector φ V) isClosed_closure)

end TernaryPoly.QuotientScalarDescent
