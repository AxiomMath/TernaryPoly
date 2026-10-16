module

public import TernaryPeriodPolynomials.Building.Integer.PathCrossProjection
public import TernaryPeriodPolynomials.Building.BadVertex.SquareCaps
public import TernaryPeriodPolynomials.Building.BadVertex.Fibers

@[expose] public section


noncomputable section
namespace TernaryPoly.BadVertexMixedProjection
open ModThreeGoodAction AugmentedFrameComplex OrientedListChains
open OrientedImageFaceProjection

local instance : DecidableEq RankTwoAugmentedFrames.RationalLine2 := Classical.decEq _

/-- The actual quotient edge of the X and Y integer fibers in the chosen integral basis. -/
def baseEdge : Finset RankTwoAugmentedFrames.RationalLine2 :=
  {RankTwoAugmentedFrames.augmentedLine 1 0,RankTwoAugmentedFrames.augmentedLine 1 1}

theorem base_vertices_distinct :
    RankTwoAugmentedFrames.augmentedLine 1 0 ≠ RankTwoAugmentedFrames.augmentedLine 1 1 :=
  fun h => (by decide : (0 : Fin 3) ≠ 1) (RankTwoAugmentedFrames.augmentedLine_injective 1 h)

/-- Exact projection of the literal two-fiber map onto its two actual quotient vertices. -/
theorem vertex_fiberMap_left (g : IntegralGL) (k : ℤ) :
    BadVertexProjection.vertex g (BadVertexSquareCaps.fiberMap g (.inl k)) =
      RankTwoAugmentedFrames.augmentedLine 1 0 :=
  BadVertexFibers.prism_fiber_vertex g 0 k

theorem vertex_fiberMap_right (g : IntegralGL) (l : ℤ) :
    BadVertexProjection.vertex g (BadVertexSquareCaps.fiberMap g (.inr l)) =
      RankTwoAugmentedFrames.augmentedLine 1 1 :=
  BadVertexFibers.prism_fiber_vertex g 1 l

/-- A local mixed block need not be a cycle: zero cross-edge component of its boundary suffices. -/
theorem cross_zero_of_projected_boundary (g : IntegralGL) (z : IntegerGridExactness.C₁)
    (hz : project (BadVertexProjection.vertex g) baseEdge
      (boundary (BadVertexSquareCaps.mixed g z)) = 0) :
    IntegerPathJoinCycles.cross (boundary (IntegerPathJoinCycles.mixed z)) = 0 := by
  exact IntegerPathCrossProjection.cross_zero_of_project_boundary
    (BadVertexSquareCaps.fiberMap g) (BadVertexFibers.xyFiber_sum_injective g)
    (BadVertexProjection.vertex g) (RankTwoAugmentedFrames.augmentedLine 1 0)
    (RankTwoAugmentedFrames.augmentedLine 1 1)
    (vertex_fiberMap_left g) (vertex_fiberMap_right g) z hz

theorem divergence_zero_of_projected_boundary (g : IntegralGL) (z : IntegerGridExactness.C₁)
    (hz : project (BadVertexProjection.vertex g) baseEdge
      (boundary (BadVertexSquareCaps.mixed g z)) = 0) :
    IntegerGridExactness.boundary₁ z = 0 := by
  simpa only [IntegerPathJoinCycles.cross_boundary_mixed] using
    cross_zero_of_projected_boundary g z hz

/-- Actual Good square caps fill every local mixed block with vanishing projected cross boundary. -/
theorem good_filling_of_projected_boundary (g : IntegralGL)
    (hb : AugmentedBadFaces.columnResidue g 0 = 0)
    (hX : AugmentedBadFaces.columnResidue g 1 ≠ 0)
    (hY : AugmentedBadFaces.columnResidue g 2 ≠ 0) (z : IntegerGridExactness.C₁)
    (hz : project (BadVertexProjection.vertex g) baseEdge
      (boundary (BadVertexSquareCaps.mixed g z)) = 0) :
    ∃ t : Chain RationalLine, t ∈ chains good 4 ∧
      boundary t = BadVertexSquareCaps.mixed g z :=
  BadVertexSquareCaps.mixed_cross_zero_bounds g hb hX hY z
    (cross_zero_of_projected_boundary g z hz)

end TernaryPoly.BadVertexMixedProjection
