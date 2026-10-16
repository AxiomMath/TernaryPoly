module

public import TernaryPeriodPolynomials.Building.AugmentedFrame.BadFaces
public import TernaryPeriodPolynomials.Building.OrientedChain.ChainProjection

@[expose] public section


noncomputable section
namespace TernaryPoly.AugmentedFrameChains
open ModThreeGoodAction AugmentedFrameComplex AugmentedBadFaces
open OrientedListChains OrientedChainProjection
local instance : DecidableEq RationalLine := fun _ _ => Classical.propDecidable _

/-- Vertices satisfy the literal arithmetic Good predicate. -/
def isGood (L : RationalLine) : Prop := Good L.val

abbrev AmbientChains (n : ℕ) := chains ambient (n+1)
abbrev GoodChains (n : ℕ) := chains good (n+1)
abbrev ProperGoodChains (n : ℕ) := chains properGood (n+1)

theorem goodChains_le (n : ℕ) : GoodChains n ≤ AmbientChains n :=
  chains_mono good_le_ambient _

theorem properGoodChains_le (n : ℕ) : ProperGoodChains n ≤ GoodChains n :=
  chains_mono properGood_le_good _

/-- The genuine ambient simplex-chain complex has no simplices of dimension above three. -/
theorem ambient_chains_eq_bot (n : ℕ) (hn : 4 < n) : chains ambient n = ⊥ := by
  classical
  apply le_antisymm ?_ bot_le
  apply Submodule.span_le.mpr
  rintro _ ⟨l,hlen,hl,rfl⟩
  change simplex l = 0
  apply simplex_eq_zero_of_not_nodup
  intro hnodup
  rcases hl with rfl | hl
  · simp only [List.length_nil] at hlen
    omega
  · have hcard := ambient_card_le_four hl
    have he : l.toFinset.card = l.length := List.toFinset_card_of_nodup hnodup
    rw [he,hlen] at hcard
    omega

theorem allowed_good_iff (l : List RationalLine) :
    Allowed good l ↔ Allowed ambient l ∧ ∀ L ∈ l, isGood L := by
  classical
  constructor
  · rintro (rfl | hl)
    · exact ⟨Or.inl rfl,by simp⟩
    · exact ⟨Or.inr hl.1,fun L hL => hl.2 L (List.mem_toFinset.mpr hL)⟩
  · rintro ⟨hl,hgood⟩
    rcases hl with rfl | hl
    · exact Or.inl rfl
    · exact Or.inr ⟨hl,fun L hL => hgood L (List.mem_toFinset.mp hL)⟩

theorem badCount_eq_zero_iff (l : List RationalLine) :
    badCount isGood l = 0 ↔ ∀ L ∈ l, isGood L := by
  classical
  rw [badCount,Finset.card_eq_zero]
  constructor
  · intro h L hL
    by_contra hn
    have hm : L ∈ badVertices isGood l := by simp [badVertices,hL,hn]
    rw [h] at hm
    exact Finset.notMem_empty L hm
  · intro h
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro L hL
    have hh : L ∈ l ∧ ¬isGood L := by simpa only [badVertices,Finset.mem_filter,List.mem_toFinset] using hL
    exact hh.2 (h L hh.1)

/-- Projecting to zero bad vertices yields an actual Good simplex chain. -/
theorem zeroBadProjection_mem_good (n : ℕ) {c : OrientedListChains.Chain RationalLine}
    (hc : c ∈ chains ambient n) : badCountProjection isGood 0 c ∈ chains good n := by
  classical
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨l,hlen,hl,rfl⟩ := hc
    by_cases hb : badCount isGood l = 0
    · rw [badCountProjection_simplex,ite_eq_left hb]
      have hg := (allowed_good_iff l).mpr ⟨hl,(badCount_eq_zero_iff l).mp hb⟩
      simpa only [hlen] using simplex_mem_chains good l hg
    · rw [badCountProjection_simplex,ite_eq_right hb]
      exact (chains good n).zero_mem
  | zero => simp
  | add c d hc hd ihc ihd => simpa only [map_add] using (chains good n).add_mem ihc ihd
  | smul q c hc ih => simpa only [map_smul] using (chains good n).smul_mem q ih

/-- Good chains are fixed pointwise by the literal zero-bad projection. -/
theorem zeroBadProjection_eq_self (n : ℕ) {c : OrientedListChains.Chain RationalLine}
    (hc : c ∈ chains good n) : badCountProjection isGood 0 c = c := by
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨l,_,hl,rfl⟩ := hc
    have hb := (badCount_eq_zero_iff l).mpr ((allowed_good_iff l).mp hl).2
    simp only [badCountProjection_simplex,hb,ite_true]
  | zero => simp
  | add c d hc hd ihc ihd => simp only [map_add,ihc,ihd]
  | smul q c hc ih => simp only [map_smul,ih]

/-- Zero-bad support is exactly the actual Good chain submodule. -/
theorem mem_good_iff_zeroBadProjection (n : ℕ) {c : OrientedListChains.Chain RationalLine}
    (hc : c ∈ chains ambient n) :
    c ∈ chains good n ↔ badCountProjection isGood 0 c = c := by
  constructor
  · exact zeroBadProjection_eq_self n
  · intro h
    rw [← h]
    exact zeroBadProjection_mem_good n hc

/-- An actual ambient simplex has at most three distinct bad vertices. -/
theorem allowed_badCount_le_three (l : List RationalLine) (hl : Allowed ambient l) :
    badCount isGood l ≤ 3 := by
  classical
  rcases hl with rfl | hl
  · simp [badCount,badVertices]
  · by_cases hb : (badVertices isGood l).Nonempty
    · apply all_bad_card_le_three
      · apply (ambient.isRelLowerSet_faces hl).2 _ hb
        intro L hL
        have hh : L ∈ l ∧ ¬isGood L := by
          simpa only [badVertices,Finset.mem_filter,List.mem_toFinset] using hL
        exact List.mem_toFinset.mpr hh.1
      · intro L hL
        have hh : L ∈ l ∧ ¬isGood L := by
          simpa only [badVertices,Finset.mem_filter,List.mem_toFinset] using hL
        exact hh.2
    · have he := Finset.not_nonempty_iff_eq_empty.mp hb
      simp only [badCount,he,Finset.card_empty,Nat.zero_le]

/-- All higher bad-count pieces vanish on the actual ambient chain complex. -/
theorem badCountProjection_eq_zero_of_three_lt (n r : ℕ) (hr : 3 < r)
    {c : OrientedListChains.Chain RationalLine} (hc : c ∈ chains ambient n) :
    badCountProjection isGood r c = 0 := by
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨l,_,hl,rfl⟩ := hc
    have hn : badCount isGood l ≠ r := ne_of_lt ((allowed_badCount_le_three l hl).trans_lt hr)
    simp only [badCountProjection_simplex,hn,ite_false]
  | zero => simp
  | add c d hc hd ihc ihd => simp only [map_add,ihc,ihd,add_zero]
  | smul q c hc ih => simp only [map_smul,ih,smul_zero]

end TernaryPoly.AugmentedFrameChains
