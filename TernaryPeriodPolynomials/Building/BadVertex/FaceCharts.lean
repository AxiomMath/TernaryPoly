module

public import TernaryPeriodPolynomials.Building.BadVertex.SimplexNormalForm
public import TernaryPeriodPolynomials.Building.BadVertex.CoherentCharts
public import TernaryPeriodPolynomials.Building.OrientedChain.ImageFaceProjection

@[expose] public section


noncomputable section
namespace TernaryPoly.BadVertexFaceCharts

open OrientedListChains OrientedImageFaceProjection

/-- A nonzero exact face component has an actual allowed, nondegenerate generating simplex.
The proof is span induction; no simplex coefficient functional or chosen basis is assumed. -/
theorem exists_supported_simplex {V W : Type*} (f : V → W)
    (C : PreAbstractSimplicialComplex V) (n : ℕ) (s : Finset W)
    {c : Chain V} (hc : c ∈ chains C n) (hne : project f s c ≠ 0) :
    ∃ l : List V, l.length = n ∧ Allowed C l ∧ l.Nodup ∧ imageFace f l = s := by
  classical
  by_contra hex
  apply hne
  clear hne
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨l,hlen,hl,rfl⟩ := hc
    by_cases hn : l.Nodup
    · by_cases hs : imageFace f l = s
      · exact (hex ⟨l,hlen,hl,hn,hs⟩).elim
      · rw [project_simplex,ite_eq_right hs]
    · rw [simplex_eq_zero_of_not_nodup l hn,map_zero]
  | zero => exact map_zero _
  | add c d hc hd ihc ihd => rw [map_add,ihc,ihd,add_zero]
  | smul q c hc ih => rw [map_smul,ih,smul_zero]

open ModThreeGoodAction AugmentedFrameComplex GoodLinkExtraction
open BadVertexProjection BadVertexCoherentCharts CoherentPrismReduction

local instance : DecidableEq RationalLine := Classical.decEq _
local instance : DecidableEq RankTwoAugmentedFrames.RationalLine2 := Classical.decEq _

/-- A nonzero component of an actual link three-chain has a genuine nondegenerate link triangle. -/
theorem exists_link_triangle (g : IntegralGL)
    (s : Finset RankTwoAugmentedFrames.RationalLine2) {c : Chain RationalLine}
    (hc : c ∈ chains (augmentedGoodLink {augmentedLine g 0}) 3)
    (hne : project (vertex g) s c ≠ 0) :
    ∃ l : List RationalLine, l.length = 3 ∧ l.Nodup ∧
      l.toFinset ∈ augmentedGoodLink {augmentedLine g 0} ∧ imageFace (vertex g) l = s := by
  obtain ⟨l,hlen,hl,hn,hs⟩ := exists_supported_simplex (vertex g) _ 3 s hc hne
  rcases hl with rfl | hl
  · simp at hlen
  · exact ⟨l,hlen,hn,hl,hs⟩

/-- Three distinct rank-two frame lines remain an actual three-element ordered list. -/
theorem quotient_triangle_nodup (q : RankTwoAugmentedFrames.IntegralGL) :
    [RankTwoAugmentedFrames.augmentedLine q 0,RankTwoAugmentedFrames.augmentedLine q 1,
      RankTwoAugmentedFrames.augmentedLine q 2].Nodup := by
  have hn : ([0,1,2] : List (Fin 3)).Nodup := by decide
  simpa only [List.map_cons,List.map_nil] using
    hn.map (RankTwoAugmentedFrames.augmentedLine_injective q)

/-- A coherent actual triangle has exactly three quotient vertices in every adapted projection. -/
theorem coherent_image_card (g h : IntegralGL)
    (hh : augmentedLine h 0 = augmentedLine g 0) :
    (imageFace (vertex g) [xFiber h 0,yFiber h 0,zFiber h 0]).card = 3 := by
  simp only [imageFace,List.map_cons,List.map_nil,xFiber,yFiber,zFiber,
    fiber_projection g h hh]
  rw [List.toFinset_card_of_nodup (quotient_triangle_nodup _)]
  rfl

/-- A mixed actual triangle has exactly the two stated quotient vertices, independently of height. -/
theorem mixed_image_eq_pair (g h : IntegralGL)
    (hh : augmentedLine h 0 = augmentedLine g 0) (k : ℤ) :
    imageFace (vertex g) [xFiber h k,xFiber h (k+1),yFiber h 0] =
      {vertex g (xFiber h 0),vertex g (yFiber h 0)} := by
  ext L
  simp only [imageFace,List.map_cons,List.map_nil,List.mem_toFinset,List.mem_cons,
    List.not_mem_nil,or_false,Finset.mem_insert,Finset.mem_singleton,xFiber,yFiber,
    fiber_projection g h hh]
  tauto

theorem projected_pair_card (g h : IntegralGL)
    (hh : augmentedLine h 0 = augmentedLine g 0) :
    ({vertex g (xFiber h 0),vertex g (yFiber h 0)} :
      Finset RankTwoAugmentedFrames.RationalLine2).card = 2 := by
  have hne : vertex g (xFiber h 0) ≠ vertex g (yFiber h 0) := by
    simp only [xFiber,yFiber,fiber_projection g h hh]
    intro he
    have hi := RankTwoAugmentedFrames.augmentedLine_injective _ he
    exact (by decide : (0 : Fin 3) ≠ 1) hi
  exact Finset.card_pair hne

/-- Every nonzero exact component has an actual adapted coherent or mixed face chart.
This realizes the finite face itself, independently of coefficient grouping. -/
theorem component_chart (g : IntegralGL) (hbad : ¬Good (augmentedLine g 0).val)
    (s : Finset RankTwoAugmentedFrames.RationalLine2) {c : Chain RationalLine}
    (hc : c ∈ chains (augmentedGoodLink {augmentedLine g 0}) 3)
    (hne : project (vertex g) s c ≠ 0) :
    ∃ h : IntegralGL, augmentedLine h 0 = augmentedLine g 0 ∧
      AugmentedPrismCaps.columnResidue h 0 = 0 ∧
      AugmentedPrismCaps.columnResidue h 1 ≠ 0 ∧
      AugmentedPrismCaps.columnResidue h 2 ≠ 0 ∧
      ((AugmentedPrismCaps.columnResidue h 1 + AugmentedPrismCaps.columnResidue h 2 ≠ 0 ∧
        s = imageFace (vertex g) [xFiber h 0,yFiber h 0,zFiber h 0]) ∨
       s = {vertex g (xFiber h 0),vertex g (yFiber h 0)}) := by
  obtain ⟨l,hlen,hn,hl,hs⟩ := exists_link_triangle g s hc hne
  obtain ⟨h,hh,hb,hX,hY,hcases⟩ := BadVertexSimplexNormalForm.triangle_normal_form
    (augmentedLine g 0) hbad l hlen hn hl
  refine ⟨h,hh,hb,hX,hY,?_⟩
  rcases hcases with ⟨hZ,hperm⟩ | ⟨k,_,hperm⟩
  · exact Or.inl ⟨hZ,hs.symm.trans (imageFace_perm (vertex g) hperm)⟩
  · exact Or.inr (hs.symm.trans ((imageFace_perm (vertex g) hperm).trans
      (mixed_image_eq_pair g h hh k)))

/-- Nonzero three-chain components have image cardinality exactly two or three. -/
theorem component_card (g : IntegralGL) (hbad : ¬Good (augmentedLine g 0).val)
    (s : Finset RankTwoAugmentedFrames.RationalLine2) {c : Chain RationalLine}
    (hc : c ∈ chains (augmentedGoodLink {augmentedLine g 0}) 3)
    (hne : project (vertex g) s c ≠ 0) : s.card = 2 ∨ s.card = 3 := by
  obtain ⟨h,hh,_,_,_,hcase⟩ := component_chart g hbad s hc hne
  rcases hcase with ⟨_,hs⟩ | hs
  · exact Or.inr (by rw [hs]; exact coherent_image_card g h hh)
  · exact Or.inl (by rw [hs]; exact projected_pair_card g h hh)

/-- A nonzero component over a three-element face has a literal coherent basis realization
with all residue hypotheses needed by the actual prism filling. -/
theorem coherent_face_chart (g : IntegralGL) (hbad : ¬Good (augmentedLine g 0).val)
    (s : Finset RankTwoAugmentedFrames.RationalLine2) (hs : s.card = 3)
    {c : Chain RationalLine} (hc : c ∈ chains (augmentedGoodLink {augmentedLine g 0}) 3)
    (hne : project (vertex g) s c ≠ 0) :
    ∃ h : IntegralGL, augmentedLine h 0 = augmentedLine g 0 ∧
      AugmentedPrismCaps.columnResidue h 0 = 0 ∧
      AugmentedPrismCaps.columnResidue h 1 ≠ 0 ∧
      AugmentedPrismCaps.columnResidue h 2 ≠ 0 ∧
      AugmentedPrismCaps.columnResidue h 1 + AugmentedPrismCaps.columnResidue h 2 ≠ 0 ∧
      s = imageFace (vertex g) [xFiber h 0,yFiber h 0,zFiber h 0] := by
  obtain ⟨h,hh,hb,hX,hY,hcase⟩ := component_chart g hbad s hc hne
  rcases hcase with ⟨hZ,he⟩ | he
  · exact ⟨h,hh,hb,hX,hY,hZ,he⟩
  · have hcard : s.card = 2 := by rw [he]; exact projected_pair_card g h hh
    omega

/-- A nonzero component over a two-element face has a literal mixed-basis realization
with the two independent Good columns and the bad first column. -/
theorem mixed_face_chart (g : IntegralGL) (hbad : ¬Good (augmentedLine g 0).val)
    (s : Finset RankTwoAugmentedFrames.RationalLine2) (hs : s.card = 2)
    {c : Chain RationalLine} (hc : c ∈ chains (augmentedGoodLink {augmentedLine g 0}) 3)
    (hne : project (vertex g) s c ≠ 0) :
    ∃ h : IntegralGL, augmentedLine h 0 = augmentedLine g 0 ∧
      AugmentedPrismCaps.columnResidue h 0 = 0 ∧
      AugmentedPrismCaps.columnResidue h 1 ≠ 0 ∧
      AugmentedPrismCaps.columnResidue h 2 ≠ 0 ∧
      s = {vertex g (xFiber h 0),vertex g (yFiber h 0)} := by
  obtain ⟨h,hh,hb,hX,hY,hcase⟩ := component_chart g hbad s hc hne
  rcases hcase with ⟨_,he⟩ | he
  · have hcard : s.card = 3 := by rw [he]; exact coherent_image_card g h hh
    omega
  · exact ⟨h,hh,hb,hX,hY,he⟩

end TernaryPoly.BadVertexFaceCharts
