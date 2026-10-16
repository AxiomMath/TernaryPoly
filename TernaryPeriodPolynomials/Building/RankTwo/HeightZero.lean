module

public import TernaryPeriodPolynomials.Building.RankTwo.HeightLinks

@[expose] public section


noncomputable section
namespace TernaryPoly.RankTwoHeightZero
open RankTwoAugmentedFrames RankTwoVertexLinks RankTwoHeightLinks
open OrientedListChains OrientedChainJoin

local instance : DecidableEq RationalLine2 := Classical.decEq _

def zeroVertex : RationalLine2 := augmentedLine 1 0

/-- There is only one rational rank-two line at last-coordinate height zero. -/
theorem height_zero_eq (L : RationalLine2) (hL : height L = 0) : L = zeroVertex := by
  have hv1 : primitiveGenerator L 1 = 0 := Int.natAbs_eq_zero.mp hL
  have hv0 : primitiveGenerator L 0 ≠ 0 := by
    intro he
    have hp := primitiveGenerator_primitive L
    simp [Primitive,content,he,hv1] at hp
  have hc : rationalVector (primitiveGenerator L) =
      (primitiveGenerator L 0 : ℚ) • template 0 := by
    funext i
    fin_cases i <;> simp [rationalVector,template,hv1]
  apply Subtype.ext
  rw [← primitiveGenerator_span L,hc,
    Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr (by exact_mod_cast hv0))]
  change _ = Submodule.span ℚ {rationalRepresentation 1 (template 0)}
  rw [map_one]
  rfl

/-- Strict Euclidean descent gives a finite actual ambient edge path from the zero line. -/
theorem vertex_path (L : RationalLine2) :
    ∃ b : Chain RationalLine2, b ∈ chains ambient 2 ∧
      boundary b = simplex [L] - simplex [zeroVertex] := by
  have aux : ∀ n : ℕ, ∀ L : RationalLine2, height L ≤ n →
      ∃ b : Chain RationalLine2, b ∈ chains ambient 2 ∧
        boundary b = simplex [L] - simplex [zeroVertex] := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro L hle
      by_cases hz : height L = 0
      · rw [height_zero_eq L hz]
        exact ⟨0,(chains ambient 2).zero_mem,by rw [map_zero,sub_self]⟩
      obtain ⟨g,hg⟩ := rationalLine_eq_augmentedLine L
      have hpos : 0 < height (augmentedLine g 0) := by rw [hg]; omega
      obtain ⟨M,hM⟩ := lowLink_nonempty g hpos
      have hml : height M < height L := by
        have he := hM.2 M (Finset.mem_singleton_self M)
        rwa [hg] at he
      obtain ⟨b,hb,hdb⟩ := ih (height M) (hml.trans_le hle) M le_rfl
      have hface : {L,M} ∈ ambient := by
        have hf := ((singleton_mem_link_iff g M).mp hM.1).2
        rwa [hg] at hf
      have hed : simplex [L,M] ∈ chains ambient 2 := by
        apply simplex_mem_chains ambient [L,M]
        apply Or.inr
        simpa only [List.toFinset_cons,List.toFinset_nil,Finset.insert_empty] using hface
      refine ⟨b - simplex [L,M],(chains ambient 2).sub_mem hb hed,?_⟩
      rw [map_sub,hdb]
      simp only [boundary_cons,boundary_nil,map_zero,sub_zero,cons_simplex]
      abel
  exact aux (height L) L le_rfl

/-- A finite actual ambient zero-chain has a filling after removing its augmentation at one vertex. -/
theorem reduced_path_filling {c : Chain RationalLine2} (hc : c ∈ chains ambient 1) :
    ∃ b : Chain RationalLine2, b ∈ chains ambient 2 ∧
      boundary b = c - cons zeroVertex (boundary c) := by
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨l,hlen,_,rfl⟩ := hc
    obtain ⟨L,rfl⟩ := List.length_eq_one_iff.mp hlen
    obtain ⟨b,hb,hdb⟩ := vertex_path L
    refine ⟨b,hb,?_⟩
    simpa only [boundary_cons,boundary_nil,map_zero,sub_zero,cons_simplex] using hdb
  | zero => exact ⟨0,(chains ambient 2).zero_mem,by simp only [map_zero,sub_zero]⟩
  | add c d hc hd ihc ihd =>
    obtain ⟨b,hb,hdb⟩ := ihc
    obtain ⟨e,he,hde⟩ := ihd
    refine ⟨b+e,(chains ambient 2).add_mem hb he,?_⟩
    rw [map_add,hdb,hde,map_add,map_add]
    abel
  | smul q c hc ih =>
    obtain ⟨b,hb,hdb⟩ := ih
    refine ⟨q • b,(chains ambient 2).smul_mem q hb,?_⟩
    rw [map_smul,hdb,smul_sub,map_smul,map_smul]

/-- Actual finite reduced H0 vanishing for the rank-two augmented-frame complex. -/
theorem ambient_reduced_zero_filling {c : Chain RationalLine2}
    (hc : c ∈ chains ambient 1) (hd : boundary c = 0) :
    ∃ b : Chain RationalLine2, b ∈ chains ambient 2 ∧ boundary b = c := by
  obtain ⟨b,hb,hdb⟩ := reduced_path_filling hc
  exact ⟨b,hb,by simpa only [hd,map_zero,sub_zero] using hdb⟩

end TernaryPoly.RankTwoHeightZero
