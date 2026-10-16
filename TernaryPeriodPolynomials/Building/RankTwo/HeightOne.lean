module

public import TernaryPeriodPolynomials.Building.RankTwo.HeightEdges
public import TernaryPeriodPolynomials.Building.RankTwo.HeightPaths

@[expose] public section


noncomputable section
namespace TernaryPoly.RankTwoHeightOne
open RankTwoAugmentedFrames RankTwoHeightLinks RankTwoHeightZero RankTwoHeightEdges
open RankTwoHeightPaths OrientedListChains OrientedChainJoin

local instance : DecidableEq RationalLine2 := Classical.decEq _

/-- An actual three-vertex ambient face gives its actual oriented triangle chain. -/
theorem triangle_chain (L M N : RationalLine2) (hface : {L,M,N} ∈ ambient) :
    simplex [L,M,N] ∈ chains ambient 3 := by
  apply simplex_mem_chains ambient [L,M,N]
  apply Or.inr
  simpa only [List.toFinset_cons,List.toFinset_nil,Finset.insert_empty] using hface

/-- Every actual edge is homologous to the difference of the fixed descending endpoint paths.
The induction uses explicit lower-vertex triangles and equal-height signed-difference subdivisions. -/
theorem edge_filling (L M : RationalLine2) (hface : {L,M} ∈ ambient) :
    ∃ b : Chain RationalLine2, b ∈ chains ambient 3 ∧
      boundary b = path M - path L - simplex [L,M] := by
  have aux : ∀ n : ℕ, ∀ L M : RationalLine2, height L + height M ≤ n →
      {L,M} ∈ ambient → ∃ b : Chain RationalLine2, b ∈ chains ambient 3 ∧
        boundary b = path M - path L - simplex [L,M] := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro L M hsum hface
      by_cases hne : L = M
      · subst M
        exact ⟨0,(chains ambient 3).zero_mem,by rw [map_zero,sub_self,simplex_repeat_adjacent,sub_zero]⟩
      rcases lt_trichotomy (height L) (height M) with hlt | he | hgt
      · have hpos : 0 < height M := by omega
        have hp := parent_lower M hpos
        have htri : {M,parent M,L} ∈ ambient := lower_triangle M (parent M) L hp hlt
          (parent_edge M hpos) (by rwa [Finset.pair_comm])
        have hep : {L,parent M} ∈ ambient := by
          apply (ambient.isRelLowerSet_faces htri).2
          · intro P hP
            simp only [Finset.mem_insert,Finset.mem_singleton] at hP ⊢
            tauto
          · simp
        obtain ⟨b,hb,hdb⟩ := ih (height L + height (parent M)) (by omega) L (parent M) le_rfl hep
        have htri' : {L,parent M,M} ∈ ambient := by
          apply (ambient.isRelLowerSet_faces htri).2
          · intro P hP
            simp only [Finset.mem_insert,Finset.mem_singleton] at hP ⊢
            tauto
          · simp
        refine ⟨b + simplex [L,parent M,M],(chains ambient 3).add_mem hb
          (triangle_chain L (parent M) M htri'),?_⟩
        rw [map_add,hdb,path_step M hpos]
        simp only [boundary_cons,boundary_nil,map_zero,sub_zero,map_sub,cons_simplex]
        abel
      · have hpos : 0 < height L := by
          by_contra hh
          have hz : height L = 0 := by omega
          exact hne ((height_zero_eq L hz).trans (height_zero_eq M (by omega)).symm)
        obtain ⟨N,hN,htri⟩ := equal_height_subdivision L M hne hface he
        have hLN : {L,N} ∈ ambient := by
          apply (ambient.isRelLowerSet_faces htri).2
          · intro P hP
            simp only [Finset.mem_insert,Finset.mem_singleton] at hP ⊢
            tauto
          · simp
        have hNM : {N,M} ∈ ambient := by
          apply (ambient.isRelLowerSet_faces htri).2
          · intro P hP
            simp only [Finset.mem_insert,Finset.mem_singleton] at hP ⊢
            tauto
          · simp
        obtain ⟨b,hb,hdb⟩ := ih (height L + height N) (by omega) L N le_rfl hLN
        obtain ⟨e,he',hde⟩ := ih (height N + height M) (by omega) N M le_rfl hNM
        have htri' : {L,N,M} ∈ ambient := by
          apply (ambient.isRelLowerSet_faces htri).2
          · intro P hP
            simp only [Finset.mem_insert,Finset.mem_singleton] at hP ⊢
            tauto
          · simp
        refine ⟨b+e+simplex [L,N,M],(chains ambient 3).add_mem
          ((chains ambient 3).add_mem hb he') (triangle_chain L N M htri'),?_⟩
        rw [map_add,map_add,hdb,hde]
        simp only [boundary_cons,boundary_nil,map_zero,sub_zero,map_sub,cons_simplex]
        abel
      · have hpos : 0 < height L := by omega
        have hp := parent_lower L hpos
        have htri := lower_triangle L (parent L) M hp hgt (parent_edge L hpos) hface
        have hep : {parent L,M} ∈ ambient := by
          apply (ambient.isRelLowerSet_faces htri).2
          · intro P hP
            simp only [Finset.mem_insert,Finset.mem_singleton] at hP ⊢
            tauto
          · simp
        obtain ⟨b,hb,hdb⟩ := ih (height (parent L) + height M) (by omega) (parent L) M le_rfl hep
        refine ⟨b+simplex [L,parent L,M],(chains ambient 3).add_mem hb
          (triangle_chain L (parent L) M htri),?_⟩
        rw [map_add,hdb,path_step L hpos]
        simp only [boundary_cons,boundary_nil,map_zero,sub_zero,map_sub,cons_simplex]
        rw [simplex_swap_eq_neg L (parent L) []]
        abel
  exact aux (height L + height M) L M le_rfl hface

/-- Finite linear extension of the explicit edge surgeries. -/
theorem one_chain_filling {c : Chain RationalLine2} (hc : c ∈ chains ambient 2) :
    ∃ b : Chain RationalLine2, b ∈ chains ambient 3 ∧
      boundary b = pathMap (boundary c) - c := by
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨l,hlen,hl,rfl⟩ := hc
    obtain ⟨L,M,rfl⟩ := List.length_eq_two.mp hlen
    have hface : {L,M} ∈ ambient := by
      simpa only [List.toFinset_cons,List.toFinset_nil,Finset.insert_empty] using
        hl.resolve_left (by simp)
    obtain ⟨b,hb,hdb⟩ := edge_filling L M hface
    exact ⟨b,hb,by rw [pathMap_boundary_edge]; exact hdb⟩
  | zero => exact ⟨0,(chains ambient 3).zero_mem,by simp only [map_zero,sub_zero]⟩
  | add c d hc hd ihc ihd =>
    obtain ⟨b,hb,hdb⟩ := ihc
    obtain ⟨e,he,hde⟩ := ihd
    refine ⟨b+e,(chains ambient 3).add_mem hb he,?_⟩
    rw [map_add,hdb,hde,map_add,map_add]
    abel
  | smul q c hc ih =>
    obtain ⟨b,hb,hdb⟩ := ih
    refine ⟨q • b,(chains ambient 3).smul_mem q hb,?_⟩
    rw [map_smul,hdb,smul_sub,map_smul,map_smul]

/-- Every finite actual rank-two ambient one-cycle has an actual finite triangle filling. -/
theorem ambient_one_cycle_filling {c : Chain RationalLine2}
    (hc : c ∈ chains ambient 2) (hd : boundary c = 0) :
    ∃ b : Chain RationalLine2, b ∈ (chains ambient 3) ∧ boundary b = c := by
  obtain ⟨b,hb,hdb⟩ := one_chain_filling hc
  refine ⟨-b,(chains ambient 3).neg_mem hb,?_⟩
  rw [map_neg,hdb,hd,map_zero,zero_sub,neg_neg]

end TernaryPoly.RankTwoHeightOne
