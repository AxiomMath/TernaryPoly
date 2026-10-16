module

public import TernaryPeriodPolynomials.Building.Ambient.RelativeHomotopy
public import TernaryPeriodPolynomials.Building.RankTwo.HeightOne

@[expose] public section

noncomputable section
namespace TernaryPoly.AmbientRelativeFilling
open ModThreeGoodAction AugmentedFrameComplex BadVertexProjection
open AmbientRelativeProjection AmbientRelativeHomotopy OrientedListChains

/-- Every finite one-cycle in an adapted actual unrestricted vertex link bounds actual triangles. -/
theorem adapted_one_cycle_filling (g : IntegralGL) {c : Chain RationalLine}
    (hc : c ∈ chains (link (augmentedLine g 0)) 2) (hd : boundary c = 0) :
    ∃ b : Chain RationalLine, b ∈ chains (link (augmentedLine g 0)) 3 ∧ boundary b = c := by
  have hproj : OrientedChainMap.map (vertex g) c ∈ chains RankTwoAugmentedFrames.ambient 2 :=
    OrientedChainMap.map_mem_chains _ _ _ (projection_mapsFaces g) 2 hc
  have hdproj : boundary (OrientedChainMap.map (vertex g) c) = 0 := by
    rw [OrientedChainMap.boundary_map,hd,map_zero]
  obtain ⟨b,hb,hdb⟩ := RankTwoHeightOne.ambient_one_cycle_filling hproj hdproj
  obtain ⟨d,hD,hdD⟩ := chain_homotopy g hc
  have hlift : OrientedChainMap.map (sectionVertex g) b ∈ chains (link (augmentedLine g 0)) 3 :=
    OrientedChainMap.map_mem_chains _ _ _ (section_mapsFaces g) 3 hb
  refine ⟨d+OrientedChainMap.map (sectionVertex g) b,(chains (link _) 3).add_mem hD hlift,?_⟩
  rw [map_add,hdD,hd,map_zero,sub_zero,OrientedChainMap.boundary_map,hdb,
    OrientedChainMap.map_comp_apply]
  abel

/-- Unrestricted actual BA₂¹ link H1 filling for every rational vertex, with no goodness assumption. -/
theorem one_cycle_filling (w : RationalLine) {c : Chain RationalLine}
    (hc : c ∈ chains (GoodLinkExtraction.goodLink ambient (fun L => L ≠ w) {w}) 2)
    (hd : boundary c = 0) :
    ∃ b : Chain RationalLine,
      b ∈ chains (GoodLinkExtraction.goodLink ambient (fun L => L ≠ w) {w}) 3 ∧ boundary b = c := by
  obtain ⟨g,hg⟩ := RationalLineBasis.rationalLine_eq_augmentedLine w
  subst w
  exact adapted_one_cycle_filling g hc hd

end TernaryPoly.AmbientRelativeFilling
