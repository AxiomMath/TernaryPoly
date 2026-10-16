module

public import TernaryPeriodPolynomials.Building.BadVertex.ProjectionChange
public import TernaryPeriodPolynomials.Building.BadVertex.FaceCharts
public import TernaryPeriodPolynomials.Building.BadVertex.MixedBlocks
public import TernaryPeriodPolynomials.Building.BadVertex.ImageSupport
public import TernaryPeriodPolynomials.Building.OrientedChain.ImageFaceDecomposition

@[expose] public section


noncomputable section
namespace TernaryPoly.BadVertexMixedFilling
open ModThreeGoodAction AugmentedFrameComplex GoodLinkExtraction BadVertexProjection
open BadVertexProjectionChange BadVertexFaceCharts BadVertexMixedBlocks
open BadVertexMixedProjection BadVertexCoherentCharts CoherentPrismReduction
open OrientedListChains OrientedImageFaceProjection OrientedImageFaceBoundary
open OrientedImageFaceDecomposition

local instance : DecidableEq RationalLine := Classical.decEq _
local instance : DecidableEq RankTwoAugmentedFrames.RationalLine2 := Classical.decEq _

/-- The standard quotient edge of an adapted chart is exactly its two projected column lines. -/
theorem baseEdge_image (g h : IntegralGL) (hh : augmentedLine h 0 = augmentedLine g 0) :
    baseEdge.image (quotientChange g h hh) =
      {vertex g (xFiber h 0),vertex g (yFiber h 0)} := by
  simp only [baseEdge,Finset.image_insert,Finset.image_singleton,quotientChange_template,
    xFiber,yFiber,fiber_projection g h hh]

/-- Every nonzero two-vertex component admits a Good filling after an actual chart change. -/
theorem edge_component_filling (g : IntegralGL) (hbad : ¬Good (augmentedLine g 0).val)
    (s : Finset RankTwoAugmentedFrames.RationalLine2) (hs : s.card = 2)
    {c : Chain RationalLine} (hc : c ∈ chains (augmentedGoodLink {augmentedLine g 0}) 3)
    (him : c ∈ imageBounded (vertex g) 2) (hd : boundary c = 0)
    (hne : project (vertex g) s c ≠ 0) :
    ∃ t : Chain RationalLine, t ∈ chains good 4 ∧ boundary t = project (vertex g) s c := by
  obtain ⟨h,hh,_,hX,hY,hface⟩ := mixed_face_chart g hbad s hs hc hne
  have hbad_h : ¬Good (augmentedLine h 0).val := by rwa [hh]
  have hc_h : c ∈ chains (augmentedGoodLink {augmentedLine h 0}) 3 := by rwa [hh]
  have him_h : c ∈ imageBounded (vertex h) 2 := imageBounded_change g h hh hbad 3 2 hc him
  obtain ⟨t,ht,hdt⟩ := edge_component_good_filling h hbad_h hX hY hc_h him_h hd
  have he := project_change g h hh hbad baseEdge 3 hc
  rw [baseEdge_image g h hh,← hface] at he
  exact ⟨t,ht,hdt.trans he.symm⟩

/-- All exact quotient-face components of an actual bounded-image link cycle bound in Good4. -/
theorem component_filling (g : IntegralGL) (hbad : ¬Good (augmentedLine g 0).val)
    {c : Chain RationalLine} (hc : c ∈ chains (augmentedGoodLink {augmentedLine g 0}) 3)
    (him : c ∈ imageBounded (vertex g) 2) (hd : boundary c = 0)
    (s : Finset RankTwoAugmentedFrames.RationalLine2) :
    ∃ t : Chain RationalLine, t ∈ chains good 4 ∧ boundary t = project (vertex g) s c := by
  by_cases hz : project (vertex g) s c = 0
  · exact ⟨0,(chains good 4).zero_mem,by rw [map_zero,hz]⟩
  rcases lt_trichotomy s.card 2 with hs | hs | hs
  · exact (hz (BadVertexImageSupport.small_project_eq_zero g hbad s hs hc)).elim
  · exact edge_component_filling g hbad s hs hc him hd hz
  · exact (hz (project_eq_zero_of_card_lt (vertex g) him s hs)).elim

/-- Every actual Good-link two-cycle supported over at most two quotient vertices per simplex
has a finite filling by actual Good four-vertex chains. -/
theorem mixed_cycle_filling (g : IntegralGL) (hbad : ¬Good (augmentedLine g 0).val)
    {c : Chain RationalLine} (hc : c ∈ chains (augmentedGoodLink {augmentedLine g 0}) 3)
    (him : c ∈ imageBounded (vertex g) 2) (hd : boundary c = 0) :
    ∃ t : Chain RationalLine, t ∈ chains good 4 ∧ boundary t = c := by
  exact fill_of_components (vertex g) (chains good 4) c (component_filling g hbad hc him hd)

end TernaryPoly.BadVertexMixedFilling
