module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.DeckConvex
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.FrameData

@[expose] public section

noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open Set Filter SymmetricSpacePositive SymmetricSpaceCharts SmoothCoveringDeRham
  SymmetricSpaceCovering SymmetricSpaceQuotientManifold

/-- The actual deck map as an open partial homeomorphism of positive coordinates. -/
def deckOpenPartialHomeomorph (g : DeckGroup) : OpenPartialHomeomorph Coordinates Coordinates where
  toFun := deckMap g
  invFun := deckMap g⁻¹
  source := positiveCoordinates
  target := positiveCoordinates
  map_source' := fun _ hx => deckMap_mem g hx
  map_target' := fun _ hx => deckMap_mem g⁻¹ hx
  left_inv' := by
    intro x hx
    rw [← deckMap_mul g⁻¹ g hx, inv_mul_cancel, deckMap_one hx]
  right_inv' := by
    intro x hx
    rw [← deckMap_mul g g⁻¹ hx, mul_inv_cancel, deckMap_one hx]
  open_source := isOpen_positiveCoordinates
  open_target := isOpen_positiveCoordinates
  continuousOn_toFun := (deckMap_smooth g).continuousOn
  continuousOn_invFun := (deckMap_smooth g⁻¹).continuousOn

/-- Actual deck images of open positive-coordinate sets are open in the ambient coordinates. -/
theorem deckMap_image_isOpen {V : Set Coordinates} (hV : IsOpen V)
    (hpos : V ⊆ positiveCoordinates) (g : DeckGroup) : IsOpen (deckMap g '' V) :=
  (deckOpenPartialHomeomorph g).isOpen_image_of_subset_source hV hpos

/-- Over a genuine smaller chart, the actual covering preimage is the union of its actual
deck-translated selected sheets. -/
theorem liftedDomain_chartOpen_eq_iUnion (S : Space) {V : Set Coordinates}
    (hV : V ⊆ (quotientChart S).target) :
    liftedDomain (chartOpen S V) = ⋃ g : DeckGroup, deckMap g '' V := by
  apply Set.ext
  intro x
  constructor
  · intro hx
    apply mem_iUnion.mpr
    refine ⟨sheetElement S x, baseCoordinate S x, baseCoordinate_mem_chartOpen S hx, ?_⟩
    exact baseCoordinate_sheet S (liftedDomain_mono (chartOpen_subset S V) hx)
  · intro hx
    obtain ⟨g,y,hy,rfl⟩ := mem_iUnion.mp hx
    exact deckMap_liftedDomain g _ (SmoothSingularComparison.chartSubset_liftedDomain S hV hy)

/-- The genuine sheet label of every point in a deck translate is exactly that deck element. -/
theorem sheetElement_deck_image (S : Space) {V : Set Coordinates}
    (hV : V ⊆ (quotientChart S).target) (g : DeckGroup) {x : Coordinates}
    (hx : x ∈ deckMap g '' V) : sheetElement S x = g := by
  obtain ⟨y,hy,rfl⟩ := hx
  rw [sheetElement_deck S g (quotientChart_target_liftedDomain S (hV hy)),
    sheetElement_chart S (hV hy), mul_one]

/-- Distinct genuine deck translates of the same selected sheet are disjoint. -/
theorem deck_images_disjoint (S : Space) {V : Set Coordinates}
    (hV : V ⊆ (quotientChart S).target) :
    Pairwise (fun g h : DeckGroup => Disjoint (deckMap g '' V) (deckMap h '' V)) := by
  intro g h hgh
  apply disjoint_left.mpr
  intro x hx hy
  exact hgh ((sheetElement_deck_image S hV g hx).symm.trans
    (sheetElement_deck_image S hV h hy))

/-- Genuine quotient projection on a selected smaller sheet has the expected image. -/
theorem coordinateProjection_image_chart (S : Space) {V : Set Coordinates}
    (hV : V ⊆ (quotientChart S).target) : coordinateProjection '' V = chartOpen S V := by
  ext q
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact (SmoothSingularComparison.chartSubset_liftedDomain S hV hx).2
  · intro hq
    refine ⟨quotientChart S q,hq.2,?_⟩
    rw [← quotientChart_projection_coordinates S (hV hq.2), (quotientChart S).left_inv hq.1]

end TernaryPoly.SmoothSingularGlobal
