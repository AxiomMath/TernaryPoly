module

public import TernaryPeriodPolynomials.Building.BadVertex.CoherentProjection
public import TernaryPeriodPolynomials.Building.Coherent.FramePermutations
public import TernaryPeriodPolynomials.Building.BadVertex.CoherentCharts
public import TernaryPeriodPolynomials.Building.BadVertex.MixedBlocks
public import TernaryPeriodPolynomials.Building.OrientedChain.SimplexPermutation

@[expose] public section


noncomputable section
namespace TernaryPoly.BadVertexCoherentBlocks
open ModThreeGoodAction AugmentedFrameComplex GoodLinkExtraction OrientedListChains
open CoherentPrismReduction BadVertexProjection BadVertexFibers BadVertexCoherentCharts
open BadVertexSimplexNormalForm OrientedImageFaceProjection OrientedSimplexPermutation
local instance : DecidableEq RationalLine := Classical.decEq _
local instance : DecidableEq RankTwoAugmentedFrames.RationalLine2 := Classical.decEq _

def baseList : List RankTwoAugmentedFrames.RationalLine2 :=
  [RankTwoAugmentedFrames.augmentedLine 1 0,RankTwoAugmentedFrames.augmentedLine 1 1,
    RankTwoAugmentedFrames.augmentedLine 1 2]

def baseFace : Finset RankTwoAugmentedFrames.RationalLine2 := baseList.toFinset

theorem baseList_nodup : baseList.Nodup := BadVertexCoherentProjection.base_triangle_nodup

theorem baseFace_card : baseFace.card = 3 := by
  rw [baseFace,List.toFinset_card_of_nodup baseList_nodup]
  rfl

theorem coherent_projected_nodup (g h : IntegralGL)
    (hh : augmentedLine h 0 = augmentedLine g 0) :
    ([xFiber h 0,yFiber h 0,zFiber h 0].map (vertex g)).Nodup := by
  let q := lowerGL (g⁻¹ * h) (first_column_lower_zero g h hh)
  have hn := (by decide : ([0,1,2] : List (Fin 3)).Nodup).map
    (RankTwoAugmentedFrames.augmentedLine_injective q)
  simpa only [List.map_cons,List.map_nil,xFiber,yFiber,zFiber,fiber_projection g h hh] using hn

/-- Aligning the actual projected order gives a single fixed integer coherent grid. -/
theorem coherent_perm_mem_range (g h : IntegralGL)
    (hh : augmentedLine h 0 = augmentedLine g 0) (l : List RationalLine)
    (hp : l.Perm [xFiber h 0,yFiber h 0,zFiber h 0])
    (he : imageFace (vertex g) l = baseFace) :
    simplex l ∈ LinearMap.range (coherentLinear g) := by
  have he' : ([xFiber h 0,yFiber h 0,zFiber h 0].map (vertex g)).toFinset = baseList.toFinset :=
    (imageFace_perm (vertex g) hp).symm.trans he
  obtain ⟨m,hm,hmap⟩ := exists_perm_map_of_toFinset (vertex g)
    [xFiber h 0,yFiber h 0,zFiber h 0] baseList (coherent_projected_nodup g h hh)
    baseList_nodup he'
  obtain ⟨q,hq,hmq⟩ := CoherentFramePermutations.exists_basis_of_perm h m hm
  rw [hmq] at hmap
  have hmap' : vertex g (xFiber q 0) = RankTwoAugmentedFrames.augmentedLine 1 0 ∧
      vertex g (yFiber q 0) = RankTwoAugmentedFrames.augmentedLine 1 1 ∧
      vertex g (zFiber q 0) = RankTwoAugmentedFrames.augmentedLine 1 2 := by
    simpa only [List.map_cons,List.map_nil,baseList,List.cons.injEq,and_true] using hmap
  obtain ⟨k,t,hx,hy,hz⟩ := coherent_chart_zero g q (hq.trans hh)
    (by simpa only [prism_fiber_vertex] using hmap'.1)
    (by simpa only [prism_fiber_vertex] using hmap'.2.1)
    (by simpa only [prism_fiber_vertex] using hmap'.2.2)
  have hme : simplex m = coherent g (k,t) := by rw [hmq,hx,hy,hz]; rfl
  obtain ⟨r,hr⟩ := simplex_perm_smul (hp.trans hm.symm)
  refine ⟨Finsupp.single (k,t) r,?_⟩
  rw [coherentLinear,Finsupp.linearCombination_single,← hme,← hr]

/-- Every actual triangle over the full base face belongs to the one coherent-grid range. -/
theorem triangle_mem_coherent_range (g : IntegralGL) (hbad : ¬Good (augmentedLine g 0).val)
    (l : List RationalLine) (hlen : l.length = 3) (hn : l.Nodup)
    (hl : l.toFinset ∈ augmentedGoodLink {augmentedLine g 0})
    (he : imageFace (vertex g) l = baseFace) :
    simplex l ∈ LinearMap.range (coherentLinear g) := by
  obtain ⟨h,hh,_,_,_,hc⟩ := triangle_normal_form _ hbad l hlen hn hl
  rcases hc with ⟨_,hp⟩ | ⟨k,_,hp⟩
  · exact coherent_perm_mem_range g h hh l hp he
  · have hep : ({vertex g (xFiber h 0),vertex g (yFiber h 0)} :
        Finset RankTwoAugmentedFrames.RationalLine2) = baseFace :=
      (BadVertexMixedBlocks.horizontal_imageFace g h hh k 0).symm.trans
        ((imageFace_perm (vertex g) hp).symm.trans he)
    have hcard : ({vertex g (xFiber h 0),vertex g (yFiber h 0)} :
        Finset RankTwoAugmentedFrames.RationalLine2).card ≤ 2 := by
      by_cases heq : vertex g (xFiber h 0) = vertex g (yFiber h 0) <;> simp [heq]
    rw [hep,baseFace_card] at hcard
    omega

/-- Finite range lifting above the standard base triangle uses actual exhaustive geometry. -/
theorem project_mem_coherent_range (g : IntegralGL) (hbad : ¬Good (augmentedLine g 0).val)
    {c : Chain RationalLine} (hc : c ∈ chains (augmentedGoodLink {augmentedLine g 0}) 3) :
    project (vertex g) baseFace c ∈ LinearMap.range (coherentLinear g) := by
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨l,hlen,hl,rfl⟩ := hc
    by_cases hn : l.Nodup
    · have hf : l.toFinset ∈ augmentedGoodLink {augmentedLine g 0} :=
        hl.resolve_left (fun he => by subst l; simp at hlen)
      by_cases he : imageFace (vertex g) l = baseFace
      · rw [project_simplex,ite_eq_left he]
        exact triangle_mem_coherent_range g hbad l hlen hn hf he
      · rw [project_simplex,ite_eq_right he]
        exact (LinearMap.range (coherentLinear g)).zero_mem
    · rw [simplex_eq_zero_of_not_nodup l hn,map_zero]
      exact (LinearMap.range (coherentLinear g)).zero_mem
  | zero => simpa only [map_zero] using (LinearMap.range (coherentLinear g)).zero_mem
  | add c d hc hd ihc ihd =>
    simpa only [map_add] using (LinearMap.range (coherentLinear g)).add_mem ihc ihd
  | smul q c hc ih =>
    simpa only [map_smul] using (LinearMap.range (coherentLinear g)).smul_mem q ih

/-- The standard coherent component of an actual link cycle is a Good boundary modulo
literal mixed triangles. -/
theorem coherent_component_reduction (g : IntegralGL)
    (hbad : ¬Good (augmentedLine g 0).val)
    (hX : AugmentedBadFaces.columnResidue g 1 ≠ 0)
    (hY : AugmentedBadFaces.columnResidue g 2 ≠ 0)
    (hZ : AugmentedBadFaces.columnResidue g 1 + AugmentedBadFaces.columnResidue g 2 ≠ 0)
    {c : Chain RationalLine} (hc : c ∈ chains (augmentedGoodLink {augmentedLine g 0}) 3)
    (hd : boundary c = 0) :
    ∃ t r : Chain RationalLine, t ∈ chains good 4 ∧ r ∈ MixedSpan g ∧
      project (vertex g) baseFace c = boundary t + r := by
  obtain ⟨a,ha⟩ := project_mem_coherent_range g hbad hc
  have hz : OrientedChainMap.map (vertex g) (coherentLinear g a) = 0 := by
    rw [ha]
    exact BadVertexCoherentProjection.component_projected_zero g hbad hc hd baseFace
  obtain ⟨t,r,ht,hr,he⟩ := BadVertexCoherentProjection.projected_coherent_reduction g
    (AugmentedBadFaces.bad_augmentedLine_residue g 0 hbad) hX hY hZ a hz
  exact ⟨t,r,ht,hr,ha.symm.trans he⟩

end TernaryPoly.BadVertexCoherentBlocks
