module

public import TernaryPeriodPolynomials.Building.BadVertex.CoherentBlocks
public import TernaryPeriodPolynomials.Building.BadVertex.FaceCharts
public import TernaryPeriodPolynomials.Building.BadVertex.ProjectionChange
public import TernaryPeriodPolynomials.Building.BadVertex.PrismSupport
public import TernaryPeriodPolynomials.Building.OrientedChain.ImageFaceDecomposition

@[expose] public section


noncomputable section
namespace TernaryPoly.BadVertexCoherentElimination
open ModThreeGoodAction AugmentedFrameComplex GoodLinkExtraction OrientedListChains
open CoherentPrismReduction BadVertexProjection BadVertexCoherentCharts
open BadVertexCoherentBlocks BadVertexFaceCharts BadVertexProjectionChange
open OrientedImageFaceProjection OrientedImageFaceBoundary OrientedImageFaceDecomposition
local instance : DecidableEq RationalLine := Classical.decEq _
local instance : DecidableEq RankTwoAugmentedFrames.RationalLine2 := Classical.decEq _

/-- A standard base triangle is transported to its actual three projected chart lines. -/
theorem baseFace_image (g h : IntegralGL) (hh : augmentedLine h 0 = augmentedLine g 0) :
    baseFace.image (quotientChange g h hh) =
      imageFace (vertex g) [xFiber h 0,yFiber h 0,zFiber h 0] := by
  simp only [baseFace,baseList,List.toFinset_cons,List.toFinset_nil,Finset.image_insert,
    Finset.image_empty,quotientChange_template,imageFace,List.map_cons,List.map_nil,
    xFiber,yFiber,zFiber,fiber_projection g h hh]

/-- A coherent component in any actual quotient chart reduces to a Good boundary and
an actual link residual with at most two projected vertices per simplex. -/
theorem triangle_component_reduction (g : IntegralGL) (hbad : ¬Good (augmentedLine g 0).val)
    (s : Finset RankTwoAugmentedFrames.RationalLine2) (hs : s.card = 3)
    {c : Chain RationalLine} (hc : c ∈ chains (augmentedGoodLink {augmentedLine g 0}) 3)
    (hd : boundary c = 0) (hne : project (vertex g) s c ≠ 0) :
    ∃ t r : Chain RationalLine, t ∈ chains good 4 ∧
      r ∈ chains (augmentedGoodLink {augmentedLine g 0}) 3 ∧
      r ∈ imageBounded (vertex g) 2 ∧ project (vertex g) s c = boundary t + r := by
  obtain ⟨h,hh,hb,hX,hY,hZ,hface⟩ := coherent_face_chart g hbad s hs hc hne
  have hbad_h : ¬Good (augmentedLine h 0).val := by rwa [hh]
  have hc_h : c ∈ chains (augmentedGoodLink {augmentedLine h 0}) 3 := by rwa [hh]
  obtain ⟨t,r,ht,hr,he⟩ := coherent_component_reduction h hbad_h hX hY hZ hc_h hd
  have hp := project_change g h hh hbad baseFace 3 hc
  rw [baseFace_image,← hface] at hp
  have hrl : r ∈ chains (augmentedGoodLink {augmentedLine g 0}) 3 := by
    have hhlink := BadVertexPrismSupport.MixedSpan_le_link h hb hX hY hZ hr
    rwa [hh] at hhlink
  exact ⟨t,r,ht,hrl,BadVertexPrismSupport.MixedSpan_le_imageBounded g h hh hr,
    hp.trans he⟩

/-- Every exact component has a supported two-image residual; zero and already-mixed
components require no correction. -/
theorem component_reduction (g : IntegralGL) (hbad : ¬Good (augmentedLine g 0).val)
    {c : Chain RationalLine} (hc : c ∈ chains (augmentedGoodLink {augmentedLine g 0}) 3)
    (hd : boundary c = 0) (s : Finset RankTwoAugmentedFrames.RationalLine2) :
    ∃ t r : Chain RationalLine, t ∈ chains good 4 ∧
      r ∈ chains (augmentedGoodLink {augmentedLine g 0}) 3 ∧
      r ∈ imageBounded (vertex g) 2 ∧ project (vertex g) s c = boundary t + r := by
  classical
  by_cases hz : project (vertex g) s c = 0
  · exact ⟨0,0,(chains good 4).zero_mem,(chains _ _).zero_mem,
      (imageBounded _ _).zero_mem,by simp only [hz,map_zero,add_zero]⟩
  rcases component_card g hbad s hc hz with hs | hs
  · refine ⟨0,project (vertex g) s c,(chains good 4).zero_mem,
      project_mem_chains _ _ _ _ hc,?_,by simp⟩
    simpa only [hs] using project_mem_imageBounded (vertex g) s c
  · obtain ⟨t,r,ht,hr,him,he⟩ := triangle_component_reduction g hbad s hs hc hd hz
    exact ⟨t,r,ht,hr,him,he⟩

/-- Every actual link two-cycle is a Good boundary plus an actual mixed-support link
cycle, by finite summation of its exact projected-face components. -/
theorem eliminate_coherent (g : IntegralGL) (hbad : ¬Good (augmentedLine g 0).val)
    {c : Chain RationalLine} (hc : c ∈ chains (augmentedGoodLink {augmentedLine g 0}) 3)
    (hd : boundary c = 0) :
    ∃ t r : Chain RationalLine, t ∈ chains good 4 ∧
      r ∈ chains (augmentedGoodLink {augmentedLine g 0}) 3 ∧
      r ∈ imageBounded (vertex g) 2 ∧ boundary r = 0 ∧ c = boundary t + r := by
  classical
  obtain ⟨S,hS,_⟩ := exists_decomposition (vertex g) c
  choose t r ht hr him he using component_reduction g hbad hc hd
  let T := ∑ s ∈ S, t s
  let R := ∑ s ∈ S, r s
  have hT : T ∈ chains good 4 := Submodule.sum_mem _ (fun s _ => ht s)
  have hR : R ∈ chains (augmentedGoodLink {augmentedLine g 0}) 3 :=
    Submodule.sum_mem _ (fun s _ => hr s)
  have hI : R ∈ imageBounded (vertex g) 2 := Submodule.sum_mem _ (fun s _ => him s)
  have hE : c = boundary T + R := by
    rw [← hS]
    simp only [he,Finset.sum_add_distrib,← map_sum]
    rfl
  have hD : boundary R = 0 := by
    have h := congrArg boundary hE
    simpa only [hd,map_add,boundary_squared,zero_add] using h.symm
  exact ⟨T,R,hT,hR,hI,hD,hE⟩

end TernaryPoly.BadVertexCoherentElimination
