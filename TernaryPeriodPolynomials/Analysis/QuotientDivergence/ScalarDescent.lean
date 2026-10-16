module

public import TernaryPeriodPolynomials.DifferentialForm.CoefficientBundle.Transitions
public import TernaryPeriodPolynomials.DifferentialForm.DeRham.Covering.Geometry

@[expose] public section


/-! Literal descent of arbitrary deck-invariant scalar functions on positive coordinates. -/
noncomputable section
namespace TernaryPoly.QuotientScalarDescent
open SymmetricSpacePositive SymmetricSpaceCharts SymmetricSpaceCovering
  SymmetricSpaceQuotientManifold PolynomialCoefficientBundle SmoothCoveringDeRham Set Filter
open scoped ContDiff Manifold Topology

def descend (f : Coordinates → ℝ) (q : OrbitSpace) : ℝ := f (coordinateChart (chosenLift q))

theorem descend_projection (f : Coordinates → ℝ)
    (hf : ∀ (g : DeckGroup) x, x ∈ positiveCoordinates → f (deckMap g x) = f x)
    (S : Space) : descend f (quotientProjection S) = f (coordinateChart S) := by
  let T := chosenLift (quotientProjection S)
  have h : deckBetween S T • S = T := deckBetween_spec S T (chosenLift_projection _)
  change f (coordinateChart T) = _
  rw [← h, ← deckMap_chart]
  exact hf _ _ (extract_mem S)

theorem descend_coordinateProjection (f : Coordinates → ℝ)
    (hf : ∀ (g : DeckGroup) x, x ∈ positiveCoordinates → f (deckMap g x) = f x)
    (x : Coordinates) (hx : x ∈ positiveCoordinates) : descend f (coordinateProjection x) = f x := by
  rw [coordinateProjection, descend_projection f hf,
    coordinateChart.right_inv (show x ∈ coordinateChart.target by simpa using hx)]

theorem descend_localLift (f : Coordinates → ℝ)
    (hf : ∀ (g : DeckGroup) x, x ∈ positiveCoordinates → f (deckMap g x) = f x)
    (S : Space) {q : OrbitSpace} (hq : q ∈ (localLift S).source) :
    descend f q = f (coordinateChart (localLift S q)) := by
  exact (congrArg (descend f) (projection_localLift S hq).symm).trans
    (descend_projection f hf (localLift S q))

theorem contMDiff_descend (f : Coordinates → ℝ) (hs : ContDiffOn ℝ ∞ f positiveCoordinates)
    (hf : ∀ (g : DeckGroup) x, x ∈ positiveCoordinates → f (deckMap g x) = f x) :
    ContMDiff 𝓘(ℝ, Coordinates) 𝓘(ℝ) ∞ (descend f) := by
  have hc : ContMDiff 𝓘(ℝ, Coordinates) 𝓘(ℝ) ∞ (fun S : Space => f (coordinateChart S)) := by
    intro S
    exact ((hs (coordinateChart S) (extract_mem S)).contDiffAt
      (isOpen_positiveCoordinates.mem_nhds (extract_mem S))).contMDiffAt.comp S (coordinateChart_contMDiff S)
  intro q
  obtain ⟨S, hS⟩ := quotientCharts_cover q
  have hq : q ∈ (localLift S).source := by simpa only [quotientChart_source] using hS
  have h := (hc (localLift S q)).comp q
    ((localLift_contMDiffOn S).contMDiffAt ((localLift S).open_source.mem_nhds hq))
  apply h.congr_of_eventuallyEq
  filter_upwards [(localLift S).open_source.mem_nhds hq] with r hr
  exact descend_localLift f hf S hr

theorem continuous_descend (f : Coordinates → ℝ) (hs : ContDiffOn ℝ ∞ f positiveCoordinates)
    (hf : ∀ (g : DeckGroup) x, x ∈ positiveCoordinates → f (deckMap g x) = f x) :
    Continuous (descend f) := (contMDiff_descend f hs hf).continuous

end TernaryPoly.QuotientScalarDescent
