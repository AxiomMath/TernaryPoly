module

public import TernaryPeriodPolynomials.DifferentialForm.Metric.Deck
public import TernaryPeriodPolynomials.DifferentialForm.DeRham.Covering.Support

@[expose] public section

/-! Scalar pairings of actual equivariant forms descend to the genuine quotient. -/
noncomputable section
namespace TernaryPoly.PolynomialFormMetric
open SymmetricSpacePositive SymmetricSpaceCharts SymmetricSpaceCovering
open SymmetricSpaceQuotientManifold PolynomialCoefficientMetric PolynomialCoefficientBundle
open SmoothCoveringDeRham SmoothLocalDeRham Set Filter
open scoped ContDiff Manifold Topology

/-- Scalar pairing on the positive covering space. -/
def coveringPairing (n k : ℕ) {U : Set OrbitSpace}
    (a b : EquivariantForm (deckRepresentation n) U k) (S : Space) : ℝ :=
  formPairing n k (coordinateChart S) (a.val.val (coordinateChart S)) (b.val.val (coordinateChart S))

theorem coveringPairing_deck (n k : ℕ) {U : Set OrbitSpace}
    (a b : EquivariantForm (deckRepresentation n) U k) (g : DeckGroup) (S : Space) :
    coveringPairing n k a b (g • S) = coveringPairing n k a b S := by
  by_cases hS : quotientProjection S ∈ U
  · have hx : coordinateChart S ∈ liftedDomain U := by
      refine ⟨extract_mem S, ?_⟩
      simpa only [Set.mem_preimage, coordinateProjection, coordinateChart.left_inv (by simp)] using hS
    simpa only [coveringPairing, deckMap_chart] using equivariant_formPairing n k a b g (coordinateChart S) hx
  · have hx : coordinateChart S ∉ liftedDomain U := by
      intro hx
      apply hS
      simpa only [Set.mem_preimage, coordinateProjection, coordinateChart.left_inv (by simp)] using hx.2
    have hg : coordinateChart (g • S) ∉ liftedDomain U := by
      intro hg
      apply hS
      simpa only [Set.mem_preimage, coordinateProjection, coordinateChart.left_inv (by simp),
        quotientProjection_quotientCovering.map_smul] using hg.2
    simp only [coveringPairing, Form.outside a.val hx, Form.outside a.val hg, formPairing_zero_left]

/-- The well-defined quotient scalar, evaluated through any chosen lift. -/
def scalarPairing (n k : ℕ) {U : Set OrbitSpace}
    (a b : EquivariantForm (deckRepresentation n) U k) (q : OrbitSpace) : ℝ :=
  coveringPairing n k a b (chosenLift q)

theorem scalarPairing_projection (n k : ℕ) {U : Set OrbitSpace}
    (a b : EquivariantForm (deckRepresentation n) U k) (S : Space) :
    scalarPairing n k a b (quotientProjection S) = coveringPairing n k a b S := by
  let T := chosenLift (quotientProjection S)
  have h : deckBetween S T • S = T := deckBetween_spec S T (chosenLift_projection _)
  change coveringPairing n k a b T = _
  rw [← h]
  exact coveringPairing_deck n k a b _ S

theorem scalarPairing_coordinateProjection (n k : ℕ) {U : Set OrbitSpace}
    (a b : EquivariantForm (deckRepresentation n) U k) (x : Coordinates) (hx : x ∈ positiveCoordinates) :
    scalarPairing n k a b (coordinateProjection x) = formPairing n k x (a.val.val x) (b.val.val x) := by
  rw [coordinateProjection, scalarPairing_projection, coveringPairing,
    coordinateChart.right_inv (show x ∈ coordinateChart.target by simpa using hx)]

theorem scalarPairing_localLift (n k : ℕ) {U : Set OrbitSpace}
    (a b : EquivariantForm (deckRepresentation n) U k) (S : Space) {q : OrbitSpace}
    (hq : q ∈ (localLift S).source) :
    scalarPairing n k a b q = coveringPairing n k a b (localLift S q) := by
  calc
    scalarPairing n k a b q = scalarPairing n k a b (quotientProjection (localLift S q)) :=
      congrArg (scalarPairing n k a b) (projection_localLift S hq).symm
    _ = _ := scalarPairing_projection n k a b _

theorem scalarPairing_nonneg (n k : ℕ) {U : Set OrbitSpace}
    (a : EquivariantForm (deckRepresentation n) U k) (q : OrbitSpace) :
    0 ≤ scalarPairing n k a a q :=
  formPairing_nonneg n k _ (extract_mem _) _

theorem scalarPairing_self_eq_zero (n k : ℕ) {U : Set OrbitSpace}
    (a : EquivariantForm (deckRepresentation n) U k) (x : Coordinates) (hx : x ∈ positiveCoordinates) :
    scalarPairing n k a a (coordinateProjection x) = 0 ↔ a.val.val x = 0 := by
  rw [scalarPairing_coordinateProjection n k a a x hx]
  exact formPairing_self_eq_zero n k x hx _

theorem scalarPairing_symm (n k : ℕ) {U : Set OrbitSpace}
    (a b : EquivariantForm (deckRepresentation n) U k) (q : OrbitSpace) :
    scalarPairing n k a b q = scalarPairing n k b a q :=
  formPairing_symm n k _ (extract_mem _) _ _

end TernaryPoly.PolynomialFormMetric
