module

public import TernaryPeriodPolynomials.Building.BadVertex.Projection
public import TernaryPeriodPolynomials.Building.RankTwo.VertexLinks

@[expose] public section

noncomputable section
namespace TernaryPoly.BadVertexProjectedCycles
open ModThreeGoodAction AugmentedFrameComplex OrientedListChains

/-- A genuine bad-vertex link two-cycle has zero projected two-chain in the actual
rank-two augmented-frame base. No rank-two H0 or H1 filling is required. -/
theorem projection_cycle_eq_zero (g : IntegralGL)
    (hbad : ¬Good (augmentedLine g 0).val) {u : Chain RationalLine}
    (hu : u ∈ chains (GoodLinkExtraction.augmentedGoodLink {augmentedLine g 0}) 3)
    (hd : boundary u = 0) : OrientedChainMap.map (BadVertexProjection.vertex g) u = 0 := by
  apply RankTwoVertexLinks.top_cycle_eq_zero
    (BadVertexProjection.transport_mem_chains g hbad 3 hu)
  rw [BadVertexProjection.boundary_transport,hd,map_zero]

/-- Two actual link two-chains with the same boundary have the same projected chain. -/
theorem projection_eq_of_boundary_eq (g : IntegralGL)
    (hbad : ¬Good (augmentedLine g 0).val) {u v : Chain RationalLine}
    (hu : u ∈ chains (GoodLinkExtraction.augmentedGoodLink {augmentedLine g 0}) 3)
    (hv : v ∈ chains (GoodLinkExtraction.augmentedGoodLink {augmentedLine g 0}) 3)
    (hd : boundary u = boundary v) :
    OrientedChainMap.map (BadVertexProjection.vertex g) u =
      OrientedChainMap.map (BadVertexProjection.vertex g) v := by
  apply sub_eq_zero.mp
  rw [← map_sub]
  exact projection_cycle_eq_zero g hbad
    ((chains (GoodLinkExtraction.augmentedGoodLink {augmentedLine g 0}) 3).sub_mem hu hv)
    (by rw [map_sub,hd,sub_self])

end TernaryPoly.BadVertexProjectedCycles
