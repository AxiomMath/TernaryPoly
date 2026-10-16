module

public import TernaryPeriodPolynomials.Building.BadTriangle.Elimination
public import TernaryPeriodPolynomials.Building.OrientedChain.ProjectionCalculus
public import TernaryPeriodPolynomials.Building.BadEdge.NormalForm
public import TernaryPeriodPolynomials.Building.BadEdge.LinkChains
public import TernaryPeriodPolynomials.Building.BadEdge.SquareCycles

@[expose] public section


noncomputable section
namespace TernaryPoly.BadEdgeElimination
open ModThreeGoodAction AugmentedFrameComplex AugmentedBadFaces AugmentedFrameChains
open OrientedListChains OrientedChainJoin OrientedChainProjection OrientedVertexExtraction
open OrientedBadFaceDecomposition AugmentedBadFaceCycles GoodLinkExtraction
open BadTriangleElimination OrientedProjectionCalculus BadEdgeLinkChains
local instance : DecidableEq RationalLine := Classical.decEq _

/-- After three-bad elimination, every exact face with more than two bad vertices vanishes. -/
theorem badFaceProjection_eq_zero_of_two_lt (s : Finset RationalLine) (hs : 2 < s.card)
    {c : Chain RationalLine} (hc : c ∈ chains ambient 4)
    (h3 : badCountProjection isGood 3 c = 0) : badFaceProjection isGood s c = 0 := by
  by_cases hcard : s.card = 3
  · exact badFace_eq_zero_of_badCount_eq_zero isGood s 3 hcard c h3
  · exact AugmentedBadFaceCycles.badFaceProjection_eq_zero_of_three_lt 4 s (by omega) hc

/-- The coefficient of a two-bad face is a genuine link one-cycle once the higher stratum vanishes. -/
theorem edge_coefficient_is_link_cycle (B : List RationalLine) (hB : B.Nodup)
    (hlen : B.length = 2) (hbad : ∀ L ∈ B, ¬isGood L)
    {c : Chain RationalLine} (hc : c ∈ chains ambient 4) (hd : boundary c ∈ chains good 3)
    (h3 : badCountProjection isGood 3 c = 0) :
    extract B (badFaceProjection isGood B.toFinset c) ∈ chains (augmentedGoodLink B.toFinset) 2 ∧
      boundary (extract B (badFaceProjection isGood B.toFinset c)) = 0 := by
  apply maximal_coefficient_is_link_cycle B hB (by intro h; simp [h] at hlen) hbad 2 3
    (by simpa only [hlen] using hc) hd
  intro s hs
  exact badFaceProjection_eq_zero_of_two_lt s (by simpa only [hlen] using hs) hc h3

/-- Every nonzero two-bad component has the actual initial-column edge normal form. -/
theorem component_normal_form (s : Finset RationalLine) (hs : s.card = 2)
    {c : Chain RationalLine} (hc : c ∈ chains ambient 4)
    (hne : badFaceProjection isGood s c ≠ 0) :
    ∃ g : IntegralGL, s = badEdge g ∧ columnResidue g 0 = 0 ∧
      columnResidue g 1 = 0 ∧ columnResidue g 2 ≠ 0 := by
  obtain ⟨hface,hbad⟩ := supported_of_badFaceProjection_ne_zero ambient isGood s
    (Finset.card_pos.mp (by omega)) 4 hc hne
  obtain ⟨g,hg,h0,h1,h2⟩ := BadEdgeNormalForm.all_bad_card_two s hface hs hbad
  refine ⟨g,?_,h0,h1,h2⟩
  ext L
  rw [hg]
  simp only [badEdge,Finset.mem_insert,Finset.mem_singleton]

/-- The standard ordered bad edge contains two distinct vertices. -/
theorem edge_nodup (g : IntegralGL) :
    ([augmentedLine g 0,augmentedLine g 1] : List RationalLine).Nodup := by
  have h01 := (augmentedLine_injective g).ne (show (0 : Fin 4) ≠ 1 by decide)
  simp [h01]

/-- The ordered first two columns realize the literal finite bad-edge set. -/
theorem edge_toFinset (g : IntegralGL) :
    ([augmentedLine g 0,augmentedLine g 1] : List RationalLine).toFinset = badEdge g := by
  ext L
  simp only [List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false,badEdge,
    Finset.mem_insert,Finset.mem_singleton]

/-- Each exact two-bad component is realized by a correcting cycle without any three-bad part. -/
theorem exists_cycle_for_component (s : Finset RationalLine) (hs : s.card = 2)
    {c : Chain RationalLine} (hc : c ∈ chains ambient 4) (hd : boundary c ∈ chains good 3)
    (h3 : badCountProjection isGood 3 c = 0) :
    ∃ z : Chain RationalLine, z ∈ chains ambient 4 ∧ boundary z = 0 ∧
      badCountProjection isGood 3 z = 0 ∧
      badCountProjection isGood 2 z = badFaceProjection isGood s c := by
  classical
  by_cases he : badFaceProjection isGood s c = 0
  · exact ⟨0,(chains ambient 4).zero_mem,by simp,by simp,by simp [he]⟩
  obtain ⟨g,hg,h0,h1,h2⟩ := component_normal_form s hs hc he
  let B : List RationalLine := [augmentedLine g 0,augmentedLine g 1]
  have hB : B.Nodup := edge_nodup g
  have hset : B.toFinset = badEdge g := edge_toFinset g
  have hsupp := supported_of_badFaceProjection_ne_zero ambient isGood s
    (Finset.card_pos.mp (by omega)) 4 hc he
  have hbad : ∀ L ∈ B, ¬isGood L := by
    intro L hL
    apply hsupp.2 L
    rw [hg,← hset]
    exact List.mem_toFinset.mpr hL
  obtain ⟨hlink,hboundary⟩ := edge_coefficient_is_link_cycle B hB rfl hbad hc hd h3
  rw [hset] at hlink hboundary
  have hlink' : extract B (badFaceProjection isGood (badEdge g) c) ∈ chains (link g) 2 := hlink
  obtain ⟨a,ha⟩ := supported_cycle_generated_by_squares g h0 h1 h2 hlink' hboundary
  obtain ⟨z,hz,hzBoundary,hzThree,hzLeading⟩ :=
    BadEdgeSquareCycles.exists_cycle_with_leading g h0 h1 h2 a
  refine ⟨z,hz,hzBoundary,hzThree,?_⟩
  change badCountProjection (fun L : RationalLine => Good L.val) 2 z = _
  rw [hzLeading,← ha,← hset]
  exact (badFaceProjection_eq_join_extract isGood B hB c).trans
    (congrArg (fun t => badFaceProjection isGood t c) (hset.trans hg.symm))

/-- Finite exact decomposition supplies a cycle correcting the entire two-bad stratum. -/
theorem exists_cycle_for_two_projection {c : Chain RationalLine}
    (hc : c ∈ chains ambient 4) (hd : boundary c ∈ chains good 3)
    (h3 : badCountProjection isGood 3 c = 0) :
    ∃ z : Chain RationalLine, z ∈ chains ambient 4 ∧ boundary z = 0 ∧
      badCountProjection isGood 3 z = 0 ∧
      badCountProjection isGood 2 z = badCountProjection isGood 2 c := by
  classical
  obtain ⟨S,hS,_⟩ := exists_badFace_decomposition isGood c
  have hlocal (s : Finset RationalLine) :
      ∃ z : Chain RationalLine, z ∈ chains ambient 4 ∧ boundary z = 0 ∧
        badCountProjection isGood 3 z = 0 ∧
        badCountProjection isGood 2 z = if s.card = 2 then badFaceProjection isGood s c else 0 := by
    by_cases hs : s.card = 2
    · simpa only [ite_eq_left hs] using exists_cycle_for_component s hs hc hd h3
    · exact ⟨0,(chains ambient 4).zero_mem,by simp,by simp,by simp [hs]⟩
  choose z hz hdzero hthree hp using hlocal
  refine ⟨∑ s ∈ S, z s,(chains ambient 4).sum_mem (fun s _ => hz s),?_,?_,?_⟩
  · simp only [map_sum,hdzero,Finset.sum_const_zero]
  · simp only [map_sum,hthree,Finset.sum_const_zero]
  · simp only [map_sum,hp]
    exact sum_card_badFaceProjection isGood 2 c S hS

/-- The finite second elimination stage preserves the boundary and kills both higher bad strata. -/
theorem eliminate_two_bad {c : Chain RationalLine}
    (hc : c ∈ chains ambient 4) (hd : boundary c ∈ chains good 3)
    (h3 : badCountProjection isGood 3 c = 0) :
    ∃ cPrime : Chain RationalLine, cPrime ∈ chains ambient 4 ∧ boundary cPrime = boundary c ∧
      badCountProjection isGood 3 cPrime = 0 ∧ badCountProjection isGood 2 cPrime = 0 := by
  obtain ⟨z,hz,hboundary,hthree,hprojection⟩ := exists_cycle_for_two_projection hc hd h3
  refine ⟨c-z,(chains ambient 4).sub_mem hc hz,?_,?_,?_⟩
  · rw [map_sub,hboundary,sub_zero]
  · rw [map_sub,h3,hthree,sub_self]
  · rw [map_sub,hprojection,sub_self]

/-- The first two finite stages together leave at most one bad vertex in every exact component. -/
theorem eliminate_three_and_two_bad {c : Chain RationalLine}
    (hc : c ∈ chains ambient 4) (hd : boundary c ∈ chains good 3) :
    ∃ cPrime : Chain RationalLine, cPrime ∈ chains ambient 4 ∧ boundary cPrime = boundary c ∧
      badCountProjection isGood 3 cPrime = 0 ∧ badCountProjection isGood 2 cPrime = 0 := by
  obtain ⟨d,hdAmbient,hdBoundary,hdThree⟩ := eliminate_three_bad hc hd
  obtain ⟨e,heAmbient,heBoundary,heThree,heTwo⟩ := eliminate_two_bad hdAmbient
    (by rw [hdBoundary]; exact hd) hdThree
  exact ⟨e,heAmbient,heBoundary.trans hdBoundary,heThree,heTwo⟩

end TernaryPoly.BadEdgeElimination
