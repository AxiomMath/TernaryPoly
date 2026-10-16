module

public import TernaryPeriodPolynomials.Building.OrientedChain.BadFaceDecomposition
public import TernaryPeriodPolynomials.Building.AugmentedFrame.BadFaceCycles
public import TernaryPeriodPolynomials.Building.BadTriangle.LinkChains
public import TernaryPeriodPolynomials.Building.BadTriangle.NeighborCycles

@[expose] public section

noncomputable section
namespace TernaryPoly.BadTriangleElimination
open ModThreeGoodAction AugmentedFrameComplex AugmentedBadFaces AugmentedFrameChains
open OrientedListChains OrientedChainJoin OrientedChainProjection OrientedVertexExtraction
open OrientedBadFaceDecomposition AugmentedBadFaceCycles GoodLinkExtraction
open BadTriangleLinkChains BadTriangleNeighborCycles
local instance : DecidableEq RationalLine := Classical.decEq _

/-- A nonempty exact bad face surviving on a supported simplex is an actual all-bad face. -/
theorem supported_bad_face {V : Type*} (C : PreAbstractSimplicialComplex V) (G : V → Prop)
    (s : Finset V) (hs : s.Nonempty) (l : List V) (hl : Allowed C l)
    (he : badVertices G l = s) : s ∈ C ∧ ∀ a ∈ s, ¬G a := by
  classical
  have hsub := subset_of_badVertices_eq G s l he
  have hbad : ∀ a ∈ s, ¬G a := by
    intro a ha
    have hm : a ∈ badVertices G l := he.symm ▸ ha
    exact (Finset.mem_filter.mp hm).2
  refine ⟨?_,hbad⟩
  rcases hl with rfl | hl
  · obtain ⟨a,ha⟩ := hs
    have h := hsub ha
    simp at h
  · exact (C.isRelLowerSet_faces hl).2 hsub hs

/-- Unsupported nonempty bad-face components vanish on actual supported chains. -/
theorem badFaceProjection_eq_zero_of_not_supported {V : Type*}
    (C : PreAbstractSimplicialComplex V) (G : V → Prop) (s : Finset V)
    (hs : s.Nonempty) (hnot : ¬(s ∈ C ∧ ∀ a ∈ s, ¬G a)) (n : ℕ)
    {c : Chain V} (hc : c ∈ chains C n) : badFaceProjection G s c = 0 := by
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨l,_,hl,rfl⟩ := hc
    have he : badVertices G l ≠ s := fun he => hnot (supported_bad_face C G s hs l hl he)
    simp only [badFaceProjection_simplex,he,ite_false]
  | zero => simp only [map_zero]
  | add c d hc hd ihc ihd => simp only [map_add,ihc,ihd,add_zero]
  | smul q c hc ih => simp only [map_smul,ih,smul_zero]

/-- A nonzero exact component detects genuine support, without assuming a simplex basis. -/
theorem supported_of_badFaceProjection_ne_zero {V : Type*}
    (C : PreAbstractSimplicialComplex V) (G : V → Prop) (s : Finset V)
    (hs : s.Nonempty) (n : ℕ) {c : Chain V} (hc : c ∈ chains C n)
    (hne : badFaceProjection G s c ≠ 0) : s ∈ C ∧ ∀ a ∈ s, ¬G a := by
  classical
  by_contra h
  exact hne (badFaceProjection_eq_zero_of_not_supported C G s hs h n hc)

/-- Cardinality projection keeps precisely the exact bad faces of that cardinality. -/
theorem badCountProjection_badFaceProjection {V : Type*} (G : V → Prop)
    (n : ℕ) (s : Finset V) (c : Chain V) :
    badCountProjection G n (badFaceProjection G s c) =
      if s.card = n then badFaceProjection G s c else 0 := by
  classical
  have he : (badCountProjection G n).comp (badFaceProjection G s) =
      if s.card = n then badFaceProjection G s else 0 := by
    apply chain_ext
    intro l
    by_cases hs : badVertices G l = s
    · by_cases hn : s.card = n <;> simp [hs,hn,badCount]
    · by_cases hn : s.card = n <;> simp [hs,hn]
  have hf := LinearMap.congr_fun he c
  split_ifs at hf ⊢ <;> exact hf

/-- Any finite exact decomposition gives a finite cardinality-filtered decomposition. -/
theorem sum_card_badFaceProjection {V : Type*} (G : V → Prop) (n : ℕ)
    (c : Chain V) (S : Finset (Finset V))
    (hS : (∑ s ∈ S, badFaceProjection G s c) = c) :
    (∑ s ∈ S, if s.card = n then badFaceProjection G s c else 0) =
      badCountProjection G n c := by
  classical
  have he := congrArg (badCountProjection G n) hS
  simpa only [map_sum,badCountProjection_badFaceProjection] using he

/-- Every nonzero three-bad component has an actual frame with the required residue pattern. -/
theorem component_normal_form (s : Finset RationalLine) (hs : s.card = 3)
    {c : Chain RationalLine} (hc : c ∈ chains ambient 4)
    (hne : badFaceProjection isGood s c ≠ 0) :
    ∃ g : IntegralGL, s = augmentedCore g ∧ columnResidue g 0 = 0 ∧
      columnResidue g 1 = 0 ∧ columnResidue g 2 ≠ 0 := by
  have hnonempty : s.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨hface,hbad⟩ := supported_of_badFaceProjection_ne_zero ambient isGood s hnonempty 4 hc hne
  obtain ⟨g,hg⟩ := all_bad_card_three_exists_core hface hs hbad
  have h0 : columnResidue g 0 = 0 :=
    bad_augmentedLine_residue g 0 (hbad _ (by rw [hg]; simp [augmentedCore]))
  have h1 : columnResidue g 1 = 0 :=
    bad_augmentedLine_residue g 1 (hbad _ (by rw [hg]; simp [augmentedCore]))
  have h2 : columnResidue g 2 ≠ 0 := by
    obtain ⟨j,hj⟩ := exists_columnResidue_ne_zero g
    fin_cases j
    · exact False.elim (hj h0)
    · exact False.elim (hj h1)
    · exact hj
  exact ⟨g,hg,h0,h1,h2⟩

/-- The standard ordered augmented core has no repeated vertices. -/
theorem core_nodup (g : IntegralGL) :
    ([augmentedLine g 0,augmentedLine g 1,augmentedLine g 3] : List RationalLine).Nodup := by
  have h01 := (augmentedLine_injective g).ne (show (0 : Fin 4) ≠ 1 by decide)
  have h03 := (augmentedLine_injective g).ne (show (0 : Fin 4) ≠ 3 by decide)
  have h13 := (augmentedLine_injective g).ne (show (1 : Fin 4) ≠ 3 by decide)
  simp [h01,h03,h13]

/-- The ordered core realizes the classified finite bad face literally. -/
theorem core_toFinset (g : IntegralGL) :
    ([augmentedLine g 0,augmentedLine g 1,augmentedLine g 3] : List RationalLine).toFinset =
      augmentedCore g := by
  ext L
  simp only [List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false,augmentedCore,
    Finset.mem_insert,Finset.mem_singleton]

/-- Each exact three-bad component is the entire three-bad part of an actual ambient cycle. -/
theorem exists_cycle_for_component (s : Finset RationalLine) (hs : s.card = 3)
    {c : Chain RationalLine} (hc : c ∈ chains ambient 4) (hd : boundary c ∈ chains good 3) :
    ∃ z : Chain RationalLine, z ∈ chains ambient 4 ∧ boundary z = 0 ∧
      badCountProjection isGood 3 z = badFaceProjection isGood s c := by
  classical
  by_cases he : badFaceProjection isGood s c = 0
  · exact ⟨0,(chains ambient 4).zero_mem,by simp,by simp [he]⟩
  obtain ⟨g,hg,h0,h1,h2⟩ := component_normal_form s hs hc he
  let B : List RationalLine := [augmentedLine g 0,augmentedLine g 1,augmentedLine g 3]
  have hB : B.Nodup := core_nodup g
  have hset : B.toFinset = augmentedCore g := core_toFinset g
  have hsupp := supported_of_badFaceProjection_ne_zero ambient isGood s
    (Finset.card_pos.mp (by omega)) 4 hc he
  have hbad : ∀ L ∈ B, ¬isGood L := by
    intro L hL
    apply hsupp.2 L
    rw [hg,← hset]
    exact List.mem_toFinset.mpr hL
  obtain ⟨hlink,hboundary⟩ := triangle_coefficient_is_link_cycle B hB rfl hbad hc hd
  rw [hset] at hlink hboundary
  obtain ⟨a,ha⟩ := exists_oriented_neighbor_combination g h0 h1 h2 hlink hboundary
  obtain ⟨z,hz,hzBoundary,hzLeading⟩ := exists_cycle_with_leading g h0 h1 h2 a
  refine ⟨z,hz,hzBoundary,?_⟩
  change badCountProjection (fun L : RationalLine => Good L.val) 3 z = _
  rw [hzLeading,← ha,← hset]
  exact (badFaceProjection_eq_join_extract isGood B hB c).trans
    (congrArg (fun t => badFaceProjection isGood t c) (hset.trans hg.symm))

/-- A finite sum of actual correcting cycles realizes the complete three-bad projection. -/
theorem exists_cycle_for_three_projection {c : Chain RationalLine}
    (hc : c ∈ chains ambient 4) (hd : boundary c ∈ chains good 3) :
    ∃ z : Chain RationalLine, z ∈ chains ambient 4 ∧ boundary z = 0 ∧
      badCountProjection isGood 3 z = badCountProjection isGood 3 c := by
  classical
  obtain ⟨S,hS,_⟩ := exists_badFace_decomposition isGood c
  have hlocal (s : Finset RationalLine) :
      ∃ z : Chain RationalLine, z ∈ chains ambient 4 ∧ boundary z = 0 ∧
        badCountProjection isGood 3 z = if s.card = 3 then badFaceProjection isGood s c else 0 := by
    by_cases hs : s.card = 3
    · simpa only [ite_eq_left hs] using exists_cycle_for_component s hs hc hd
    · exact ⟨0,(chains ambient 4).zero_mem,by simp,by simp [hs]⟩
  choose z hz hdzero hp using hlocal
  refine ⟨∑ s ∈ S, z s,(chains ambient 4).sum_mem (fun s _ => hz s),?_,?_⟩
  · simp only [map_sum,hdzero,Finset.sum_const_zero]
  · simp only [map_sum,hp]
    exact sum_card_badFaceProjection isGood 3 c S hS

/-- The finite first elimination stage preserves the boundary and removes every three-bad term. -/
theorem eliminate_three_bad {c : Chain RationalLine}
    (hc : c ∈ chains ambient 4) (hd : boundary c ∈ chains good 3) :
    ∃ cPrime : Chain RationalLine, cPrime ∈ chains ambient 4 ∧ boundary cPrime = boundary c ∧
      badCountProjection isGood 3 cPrime = 0 := by
  obtain ⟨z,hz,hboundary,hprojection⟩ := exists_cycle_for_three_projection hc hd
  refine ⟨c-z,(chains ambient 4).sub_mem hc hz,?_,?_⟩
  · rw [map_sub,hboundary,sub_zero]
  · rw [map_sub,hprojection,sub_self]

end TernaryPoly.BadTriangleElimination
