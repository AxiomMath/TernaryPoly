module

public import TernaryPeriodPolynomials.Building.AugmentedFrame.FrameChains
public import TernaryPeriodPolynomials.Building.Good.LinkExtraction
public import TernaryPeriodPolynomials.Building.MaximalBadFaceCycle

@[expose] public section

noncomputable section
namespace TernaryPoly.AugmentedBadFaceCycles
open ModThreeGoodAction AugmentedFrameComplex AugmentedFrameChains
open OrientedListChains OrientedChainProjection OrientedVertexExtraction
open GoodLinkExtraction MaximalBadFaceCycle
local instance : DecidableEq RationalLine := Classical.decEq _

/-- Actual ambient chains have no exact bad-face component with more than three vertices. -/
theorem badFaceProjection_eq_zero_of_three_lt (n : ℕ) (s : Finset RationalLine)
    (hs : 3 < s.card) {c : Chain RationalLine} (hc : c ∈ chains ambient n) :
    badFaceProjection isGood s c = 0 := by
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨l,_,hl,rfl⟩ := hc
    have hn : badVertices isGood l ≠ s := by
      intro he
      have hb := allowed_badCount_le_three l hl
      rw [badCount,he] at hb
      omega
    simp only [badFaceProjection_simplex,hn,ite_false]
  | zero => simp
  | add c d hc hd ihc ihd => simp only [map_add,ihc,ihd,add_zero]
  | smul q c hc ih => simp only [map_smul,ih,smul_zero]

/-- The empty exact bad-face projection fixes every actual Good chain. -/
theorem empty_badFaceProjection_eq_self (n : ℕ) {c : Chain RationalLine}
    (hc : c ∈ chains good n) : badFaceProjection isGood ∅ c = c := by
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨l,_,hl,rfl⟩ := hc
    have hz := (badCount_eq_zero_iff l).mpr ((allowed_good_iff l).mp hl).2
    have he : badVertices isGood l = ∅ := Finset.card_eq_zero.mp hz
    simp only [badFaceProjection_simplex,he,ite_true]
  | zero => simp
  | add c d hc hd ihc ihd => simp only [map_add,ihc,ihd]
  | smul q c hc ih => simp only [map_smul,ih]

/-- At any maximal nonempty bad face, the extracted coefficient is an actual Good-link cycle. -/
theorem maximal_coefficient_is_link_cycle (B : List RationalLine) (hB : B.Nodup)
    (hne : B ≠ []) (hbad : ∀ L ∈ B, ¬isGood L) (n m : ℕ) {c : Chain RationalLine}
    (hc : c ∈ chains ambient (n+B.length)) (hd : boundary c ∈ chains good m)
    (hmax : ∀ s : Finset RationalLine, B.length < s.card → badFaceProjection isGood s c = 0) :
    extract B (badFaceProjection isGood B.toFinset c) ∈ chains (augmentedGoodLink B.toFinset) n ∧
    boundary (extract B (badFaceProjection isGood B.toFinset c)) = 0 := by
  refine ⟨ambient_extract_mem_goodLink B hB hbad n hc,?_⟩
  exact boundary_extract_projection_eq_zero isGood B hB hne hbad c hmax
    (empty_badFaceProjection_eq_self m hd)

/-- The three-bad coefficient of every actual tetrahedron chain with Good boundary is a reduced
zero-cycle in the genuine Good link of that bad triangle. No filling hypothesis is needed. -/
theorem triangle_coefficient_is_link_cycle (B : List RationalLine) (hB : B.Nodup)
    (hlen : B.length = 3) (hbad : ∀ L ∈ B, ¬isGood L) {c : Chain RationalLine}
    (hc : c ∈ chains ambient 4) (hd : boundary c ∈ chains good 3) :
    extract B (badFaceProjection isGood B.toFinset c) ∈ chains (augmentedGoodLink B.toFinset) 1 ∧
    boundary (extract B (badFaceProjection isGood B.toFinset c)) = 0 := by
  apply maximal_coefficient_is_link_cycle B hB (by intro h; simp [h] at hlen) hbad 1 3
    (by simpa only [hlen] using hc) hd
  intro s hs
  exact badFaceProjection_eq_zero_of_three_lt 4 s (by simpa only [hlen] using hs) hc

end TernaryPoly.AugmentedBadFaceCycles
