module

public import TernaryPeriodPolynomials.Building.BadVertex.Fibers
public import TernaryPeriodPolynomials.Building.OrientedChain.SimplexCoefficient
public import TernaryPeriodPolynomials.Building.BadVertex.ProjectedCycles
public import TernaryPeriodPolynomials.Building.OrientedChain.ImageFaceProjection

@[expose] public section


noncomputable section
namespace TernaryPoly.BadVertexCoherentProjection
open ModThreeGoodAction AugmentedFrameComplex OrientedListChains CoherentPrismReduction AugmentedPrismCaps
open OrientedVertexChains OrientedSimplexCoefficient

/-- All coherent triangles in the same actual chart have the same literal projected orientation. -/
theorem coherent_vertices_project (g : IntegralGL) (p : ℤ × ℤ) :
    [xFiber g p.1,yFiber g p.2,zFiber g (p.1+p.2)].map (BadVertexProjection.vertex g) =
      [RankTwoAugmentedFrames.augmentedLine 1 0,
        RankTwoAugmentedFrames.augmentedLine 1 1,
        RankTwoAugmentedFrames.augmentedLine 1 2] := by
  simp only [List.map_cons,List.map_nil,BadVertexFibers.prism_fiber_vertex]

theorem base_triangle_nodup :
    [RankTwoAugmentedFrames.augmentedLine 1 0,
      RankTwoAugmentedFrames.augmentedLine 1 1,
      RankTwoAugmentedFrames.augmentedLine 1 2].Nodup := by
  simpa only [List.map_cons,List.map_nil] using
    (List.nodup_cons.mpr ⟨by decide,List.nodup_cons.mpr ⟨by decide,
      List.nodup_cons.mpr ⟨by simp,List.nodup_nil⟩⟩⟩ :
        ([0,1,2] : List (Fin 3)).Nodup).map (RankTwoAugmentedFrames.augmentedLine_injective 1)

/-- Actual projection of a finite coherent combination detects its entire augmentation. -/
theorem augmentation_eq_zero_of_projected (g : IntegralGL) (a : IntegerGridExactness.C₀)
    (ha : OrientedChainMap.map (BadVertexProjection.vertex g) (coherentLinear g a) = 0) :
    IntegerGridExactness.augmentation a = 0 := by
  have he := coefficientSum_eq_zero_of_map (BadVertexProjection.vertex g)
    (fun p : ℤ × ℤ => [xFiber g p.1,yFiber g p.2,zFiber g (p.1+p.2)]) _
    base_triangle_nodup (coherent_vertices_project g) a ha
  exact he

/-- A coherent combination with zero projected chain is an actual Good boundary modulo
literal adjacent-fiber mixed triangles. -/
theorem projected_coherent_reduction (g : IntegralGL) (hb : columnResidue g 0 = 0)
    (hX : columnResidue g 1 ≠ 0) (hY : columnResidue g 2 ≠ 0)
    (hZ : columnResidue g 1 + columnResidue g 2 ≠ 0) (a : IntegerGridExactness.C₀)
    (ha : OrientedChainMap.map (BadVertexProjection.vertex g) (coherentLinear g a) = 0) :
    ∃ t r : Chain RationalLine, t ∈ chains good 4 ∧ r ∈ MixedSpan g ∧
      coherentLinear g a = boundary t + r :=
  coherent_augmentation_zero g hb hX hY hZ a (augmentation_eq_zero_of_projected g a ha)

/-- Every exact projected-face component of an actual link cycle has zero projected chain. -/
theorem component_projected_zero (g : IntegralGL)
    (hbad : ¬Good (augmentedLine g 0).val) {u : Chain RationalLine}
    (hu : u ∈ chains (GoodLinkExtraction.augmentedGoodLink {augmentedLine g 0}) 3)
    (hd : boundary u = 0) (s : Finset RankTwoAugmentedFrames.RationalLine2) :
    OrientedChainMap.map (BadVertexProjection.vertex g)
      (OrientedImageFaceProjection.project (BadVertexProjection.vertex g) s u) = 0 :=
  OrientedImageFaceProjection.map_project_eq_zero _ s
    (BadVertexProjectedCycles.projection_cycle_eq_zero g hbad hu hd)

end TernaryPoly.BadVertexCoherentProjection
