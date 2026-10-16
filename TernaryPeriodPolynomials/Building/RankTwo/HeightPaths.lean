module

public import TernaryPeriodPolynomials.Building.RankTwo.HeightZero

@[expose] public section


noncomputable section
namespace TernaryPoly.RankTwoHeightPaths
open RankTwoAugmentedFrames RankTwoVertexLinks RankTwoHeightLinks RankTwoHeightZero
open OrientedListChains OrientedChainJoin

local instance : DecidableEq RationalLine2 := Classical.decEq _

/-- An actual lower ambient neighbor at every positive-height vertex. -/
theorem exists_lower_neighbor (L : RationalLine2) (hL : 0 < height L) :
    ∃ M : RationalLine2, height M < height L ∧ {L,M} ∈ ambient := by
  obtain ⟨g,hg⟩ := rationalLine_eq_augmentedLine L
  obtain ⟨M,hM⟩ := lowLink_nonempty g (by rwa [hg])
  refine ⟨M,?_,?_⟩
  · have hm := hM.2 M (Finset.mem_singleton_self M)
    rwa [hg] at hm
  · have hm := ((singleton_mem_link_iff g M).mp hM.1).2
    rwa [hg] at hm

/-- Fix one lower neighbor once, so endpoint paths are coherent under recursion. -/
def parent (L : RationalLine2) : RationalLine2 :=
  if hL : 0 < height L then (exists_lower_neighbor L hL).choose else zeroVertex

theorem parent_lower (L : RationalLine2) (hL : 0 < height L) : height (parent L) < height L := by
  rw [parent,dite_eq_left hL]
  exact (exists_lower_neighbor L hL).choose_spec.1

theorem parent_edge (L : RationalLine2) (hL : 0 < height L) : {L,parent L} ∈ ambient := by
  rw [parent,dite_eq_left hL]
  exact (exists_lower_neighbor L hL).choose_spec.2

/-- The finite actual path from the height-zero line follows the chosen descending neighbors. -/
def path (L : RationalLine2) : Chain RationalLine2 :=
  if _hL : 0 < height L then path (parent L) + simplex [parent L,L] else 0
termination_by height L
decreasing_by exact parent_lower L _hL

theorem path_step (L : RationalLine2) (hL : 0 < height L) :
    path L = path (parent L) + simplex [parent L,L] := by rw [path,dite_eq_left hL]

theorem path_zero (L : RationalLine2) (hL : height L = 0) : path L = 0 := by
  rw [path,dite_eq_right (by omega)]

theorem parent_edge_chain (L : RationalLine2) (hL : 0 < height L) :
    simplex [parent L,L] ∈ chains ambient 2 := by
  apply simplex_mem_chains ambient [parent L,L]
  apply Or.inr
  simpa only [List.toFinset_cons,List.toFinset_nil,Finset.insert_empty,Finset.pair_comm]
    using parent_edge L hL

theorem path_mem (L : RationalLine2) : path L ∈ chains ambient 2 := by
  by_cases hL : 0 < height L
  · rw [path_step L hL]
    exact (chains ambient 2).add_mem (path_mem (parent L)) (parent_edge_chain L hL)
  · rw [path_zero L (by omega)]
    exact (chains ambient 2).zero_mem
termination_by height L
decreasing_by exact parent_lower L hL

/-- The descending path has its literal two endpoints. -/
theorem path_boundary (L : RationalLine2) :
    boundary (path L) = simplex [L] - simplex [zeroVertex] := by
  by_cases hL : 0 < height L
  · rw [path_step L hL,map_add,path_boundary (parent L)]
    simp only [boundary_cons,boundary_nil,map_zero,sub_zero,cons_simplex]
    abel
  · have hz : height L = 0 := by omega
    rw [path_zero L hz,map_zero,height_zero_eq L hz,sub_self]
termination_by height L
decreasing_by exact parent_lower L hL

/-- Singleton evaluation extends the endpoint paths through the actual alternating quotient. -/
def pathValue : List RationalLine2 → Chain RationalLine2
  | [L] => path L
  | _ => 0

theorem pathValue_alternating : SpanChainComparison.AlternatingLists pathValue := by
  intro p a b s
  cases p with
  | nil => simp [pathValue]
  | cons n p => cases p <;> simp [pathValue]

def pathMap : Chain RationalLine2 →ₗ[ℚ] Chain RationalLine2 :=
  SpanChainComparison.evaluate pathValue pathValue_alternating

@[simp] theorem pathMap_singleton (L : RationalLine2) : pathMap (simplex [L]) = path L :=
  SpanChainComparison.evaluate_simplex pathValue pathValue_alternating [L]

theorem pathMap_boundary_edge (L M : RationalLine2) :
    pathMap (boundary (simplex [L,M])) = path M - path L := by
  simp only [boundary_cons,boundary_nil,map_zero,sub_zero,cons_simplex,map_sub,pathMap_singleton]

end TernaryPoly.RankTwoHeightPaths
