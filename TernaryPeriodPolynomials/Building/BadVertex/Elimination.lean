module

public import TernaryPeriodPolynomials.Building.BadTriangle.Elimination
public import TernaryPeriodPolynomials.Building.OrientedChain.ProjectionCalculus

@[expose] public section

noncomputable section
namespace TernaryPoly.BadVertexElimination
open ModThreeGoodAction AugmentedFrameComplex AugmentedBadFaces AugmentedFrameChains
open OrientedListChains OrientedChainJoin OrientedChainProjection OrientedVertexExtraction
open OrientedBadFaceDecomposition AugmentedBadFaceCycles GoodLinkExtraction
open BadTriangleElimination OrientedProjectionCalculus
local instance : DecidableEq RationalLine := Classical.decEq _

/-- The exact remaining bad-vertex filling obligation. It concerns inclusion into Good chains,
not filling inside the link itself. -/
def LinkBoundaryFilling : Prop :=
  ∀ a : RationalLine, ¬isGood a → ∀ u : Chain RationalLine,
    u ∈ chains (augmentedGoodLink {a}) 3 → boundary u = 0 →
      ∃ t : Chain RationalLine, t ∈ chains good 4 ∧ boundary t = u

/-- Once the two higher bad strata vanish, every bad face of size at least two vanishes. -/
theorem higher_faces_eq_zero {c : Chain RationalLine} (hc : c ∈ chains ambient 4)
    (h2 : badCountProjection isGood 2 c = 0) (h3 : badCountProjection isGood 3 c = 0)
    (s : Finset RationalLine) (hs : 1 < s.card) : badFaceProjection isGood s c = 0 := by
  by_cases hs2 : s.card = 2
  · exact badFace_eq_zero_of_badCount_eq_zero isGood s 2 hs2 c h2
  by_cases hs3 : s.card = 3
  · exact badFace_eq_zero_of_badCount_eq_zero isGood s 3 hs3 c h3
  exact badFaceProjection_eq_zero_of_three_lt 4 s (by omega) hc

/-- Each exact component has a Good replacement with the same boundary, assuming precisely
the remaining local inclusion-boundary obligation. -/
theorem component_good_replacement (hfill : LinkBoundaryFilling)
    {c : Chain RationalLine} (hc : c ∈ chains ambient 4) (hd : boundary c ∈ chains good 3)
    (h2 : badCountProjection isGood 2 c = 0) (h3 : badCountProjection isGood 3 c = 0)
    (s : Finset RationalLine) :
    ∃ t : Chain RationalLine, t ∈ chains good 4 ∧ boundary t = boundary (badFaceProjection isGood s c) := by
  classical
  by_cases hzero : badFaceProjection isGood s c = 0
  · exact ⟨0,(chains good 4).zero_mem,by simp [hzero]⟩
  by_cases hempty : s = ∅
  · subst s
    refine ⟨badFaceProjection isGood ∅ c,?_,rfl⟩
    rw [← badCount_zero_eq_badFace_empty]
    exact zeroBadProjection_mem_good 4 hc
  have hcard : s.card = 1 := by
    have hpos : 0 < s.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hempty)
    by_contra hne
    exact hzero (higher_faces_eq_zero hc h2 h3 s (by omega))
  obtain ⟨a,rfl⟩ := Finset.card_eq_one.mp hcard
  have hbad : ¬isGood a :=
    (supported_of_badFaceProjection_ne_zero ambient isGood {a} (by simp) 4 hc hzero).2 a (by simp)
  have hlist : ([a] : List RationalLine).toFinset = {a} := by simp
  obtain ⟨hu,hdu⟩ := maximal_coefficient_is_link_cycle [a] (by simp) (by simp)
    (by intro b hb; simpa using (List.mem_singleton.mp hb) ▸ hbad) 3 3 hc hd
    (fun s hs => higher_faces_eq_zero hc h2 h3 s hs)
  rw [hlist] at hu hdu
  obtain ⟨t,ht,hdt⟩ := hfill a hbad _ hu hdu
  refine ⟨t,ht,?_⟩
  have hfactor := badFaceProjection_eq_join_extract isGood [a] (by simp) c
  rw [hlist] at hfactor
  rw [← hfactor,boundary_join_simplex]
  simp only [boundary_cons,boundary_nil,map_zero,sub_zero,List.length_singleton,
    pow_one,join_simplex_left,prependList,LinearMap.id_apply,hdu,map_zero,smul_zero,add_zero]
  exact hdt

/-- Finite summation completes the last bad-stratum elimination under the exact local filling
premise. No ambient connectivity or link-generation assertion is assumed implicitly. -/
theorem eliminate_one_bad (hfill : LinkBoundaryFilling)
    {c : Chain RationalLine} (hc : c ∈ chains ambient 4) (hd : boundary c ∈ chains good 3)
    (h2 : badCountProjection isGood 2 c = 0) (h3 : badCountProjection isGood 3 c = 0) :
    ∃ t : Chain RationalLine, t ∈ chains good 4 ∧ boundary t = boundary c := by
  classical
  obtain ⟨S,hS,_⟩ := exists_badFace_decomposition isGood c
  have hlocal := component_good_replacement hfill hc hd h2 h3
  choose t ht hdt using hlocal
  refine ⟨∑ s ∈ S, t s,(chains good 4).sum_mem (fun s _ => ht s),?_⟩
  rw [map_sum]
  simp_rw [hdt]
  rw [← map_sum,hS]

end TernaryPoly.BadVertexElimination
