module

public import TernaryPeriodPolynomials.DifferentialForm.DeRham.Covering.Operations
public import TernaryPeriodPolynomials.SymmetricSpace.Quotient.ManifoldProjection

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothCoveringDeRham
open Set Filter SymmetricSpacePositive SymmetricSpaceCharts SymmetricSpaceCovering
  SymmetricSpaceQuotientManifold
open scoped ContDiff Topology

/-- The true deck coordinate map: normalized congruence by the actual principal-six matrix. -/
def deckMap (g : DeckGroup) : Coordinates → Coordinates :=
  coordinateAction (SymmetricSpaceArithmeticProper.realIntegral (deckInclusion g))

theorem deckMap_smooth (g : DeckGroup) : ContDiffOn ℝ ∞ (deckMap g) positiveCoordinates :=
  contDiffOn_coordinateAction _

theorem deckMap_mem (g : DeckGroup) {x : Coordinates} (hx : x ∈ positiveCoordinates) :
    deckMap g x ∈ positiveCoordinates := coordinateAction_mem _ x hx

theorem deckMap_chart (g : DeckGroup) (S : Space) :
    deckMap g (coordinateChart S) = coordinateChart (g • S) :=
  (coordinates_deck_smul g S).symm

theorem deckMap_inverseChart (g : DeckGroup) {x : Coordinates} (hx : x ∈ positiveCoordinates) :
    coordinateChart.symm (deckMap g x) = g • coordinateChart.symm x := by
  apply coordinateChart.injOn (by simp) (by simp)
  rw [coordinateChart.right_inv (by simpa using deckMap_mem g hx), ← deckMap_chart,
    coordinateChart.right_inv (by simpa using hx)]

theorem deckMap_one {x : Coordinates} (hx : x ∈ positiveCoordinates) : deckMap 1 x = x := by
  have he := coordinateChart.right_inv (show x ∈ coordinateChart.target by simpa using hx)
  calc
    deckMap 1 x = deckMap 1 (coordinateChart (coordinateChart.symm x)) := congrArg _ he.symm
    _ = coordinateChart ((1 : DeckGroup) • coordinateChart.symm x) := deckMap_chart _ _
    _ = x := by rw [one_smul, he]

theorem deckMap_mul (g h : DeckGroup) {x : Coordinates} (hx : x ∈ positiveCoordinates) :
    deckMap (g * h) x = deckMap g (deckMap h x) := by
  have he : x = coordinateChart (coordinateChart.symm x) :=
    (coordinateChart.right_inv (by simpa using hx)).symm
  conv_lhs => rw [he]
  rw [deckMap_chart, mul_smul, ← deckMap_chart, ← deckMap_chart,
    coordinateChart.right_inv (by simpa using hx)]

/-- The actual quotient projection in global positive coordinates. -/
def coordinateProjection (x : Coordinates) : OrbitSpace :=
  quotientProjection (coordinateChart.symm x)

theorem coordinateProjection_continuousOn : ContinuousOn coordinateProjection positiveCoordinates := by
  exact quotientProjection_covering.continuous.comp_continuousOn
    (coordinateChart.continuousOn_symm.mono (by simp))

theorem coordinateProjection_deck (g : DeckGroup) {x : Coordinates} (hx : x ∈ positiveCoordinates) :
    coordinateProjection (deckMap g x) = coordinateProjection x := by
  unfold coordinateProjection
  rw [deckMap_inverseChart g hx, quotientProjection_quotientCovering.map_smul]

/-- The covering domain lying over an actual quotient open set. -/
def liftedDomain (U : Set OrbitSpace) : Set Coordinates :=
  positiveCoordinates ∩ coordinateProjection ⁻¹' U

theorem liftedDomain_isOpen {U : Set OrbitSpace} (hU : IsOpen U) : IsOpen (liftedDomain U) := by
  exact coordinateProjection_continuousOn.isOpen_inter_preimage isOpen_positiveCoordinates hU

theorem deckMap_liftedDomain (g : DeckGroup) (U : Set OrbitSpace) :
    MapsTo (deckMap g) (liftedDomain U) (liftedDomain U) := by
  intro x hx
  exact ⟨deckMap_mem g hx.1, by simpa [coordinateProjection_deck g hx.1] using hx.2⟩

@[simp] theorem liftedDomain_univ : liftedDomain Set.univ = positiveCoordinates := by
  simp [liftedDomain]

theorem quotientChart_projection_coordinates (S : Space) {x : Coordinates}
    (hx : x ∈ (quotientChart S).target) :
    (quotientChart S).symm x = coordinateProjection x := by
  rw [quotientChart_inverse S x hx]
  unfold coordinateProjection
  congr 1
  apply Subtype.ext
  exact (coordinateChart_inverse x (quotientChart_target_subset S hx)).symm

/-- The distinguished chart sheet is included in its actual covering preimage. -/
theorem quotientChart_target_liftedDomain (S : Space) :
    (quotientChart S).target ⊆ liftedDomain (quotientChart S).source := by
  intro x hx
  exact ⟨quotientChart_target_subset S hx, by
    change coordinateProjection x ∈ (quotientChart S).source
    rw [← quotientChart_projection_coordinates S hx]
    exact (quotientChart S).map_target hx⟩

end TernaryPoly.SmoothCoveringDeRham
