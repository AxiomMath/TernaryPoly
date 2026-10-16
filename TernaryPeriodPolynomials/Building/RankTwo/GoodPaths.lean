module

public import TernaryPeriodPolynomials.Building.RankTwo.GoodComplex

@[expose] public section


noncomputable section
namespace TernaryPoly.RankTwoGoodPaths
open RankTwoAugmentedFrames RankTwoVertexLinks RankTwoGoodComplex
open OrientedListChains OrientedChainJoin
local instance : DecidableEq RationalLine2 := Classical.decEq _

/-- The explicit finite integer path between two indices in the actual oriented chain model. -/
theorem integer_path (k l : ℤ) :
    ∃ b : Chain ℤ, b ∈ chains IntegerPathChains.pathComplex 2 ∧
      boundary b = simplex [l] - simplex [k] := by
  let b := IntegerPathChains.edgeTransport (IntegerPathExactness.path l - IntegerPathExactness.path k)
  refine ⟨b.val,b.property,?_⟩
  have he := congrArg Subtype.val (IntegerPathChains.differential_edgeTransport
    (IntegerPathExactness.path l - IntegerPathExactness.path k))
  change boundary b.val = _ at he
  rw [map_sub,IntegerPathExactness.boundary_path,IntegerPathExactness.boundary_path,
    map_sub,map_sub,map_sub,IntegerPathChains.vertexTransport_vertex,
    IntegerPathChains.vertexTransport_vertex,IntegerPathChains.vertexTransport_vertex] at he
  change boundary b.val = (simplex [l] - simplex [0]) - (simplex [k] - simplex [0]) at he
  rw [he]
  abel

/-- The full actual link of any rank-two vertex is connected by finite integer paths. -/
theorem vertexLink_path (g : IntegralGL) (L M : RationalLine2)
    (hL : {L} ∈ vertexLink g) (hM : {M} ∈ vertexLink g) :
    ∃ b : Chain RationalLine2, b ∈ chains (vertexLink g) 2 ∧
      boundary b = simplex [M] - simplex [L] := by
  obtain ⟨k,rfl⟩ := exists_coordinate g L hL
  obtain ⟨l,rfl⟩ := exists_coordinate g M hM
  obtain ⟨b,hb,hdb⟩ := integer_path k l
  refine ⟨OrientedChainMap.map (coordinateLine g) b,
    OrientedChainMap.map_mem_chains (coordinateLine g) IntegerPathChains.pathComplex
      (vertexLink g) (coordinate_maps_faces g) 2 hb,?_⟩
  rw [OrientedChainMap.boundary_map,hdb,map_sub]
  simp only [OrientedChainMap.map_simplex,List.map_cons,List.map_nil]

/-- The link path around a bad vertex lies entirely in the actual Good subcomplex. -/
theorem bad_neighbor_path (φ : Functional) (hφ : φ ≠ 0) (L M N : RationalLine2)
    (hL : ¬Good φ L) (hM : M ≠ L) (hN : N ≠ L)
    (hfM : {L,M} ∈ ambient) (hfN : {L,N} ∈ ambient) :
    ∃ b : Chain RationalLine2, b ∈ chains (good φ) 2 ∧
      boundary b = simplex [N] - simplex [M] := by
  obtain ⟨g,hg⟩ := rationalLine_eq_augmentedLine L
  have hm : {M} ∈ vertexLink g := (singleton_mem_link_iff g M).mpr (by simpa only [hg] using And.intro hM hfM)
  have hn : {N} ∈ vertexLink g := (singleton_mem_link_iff g N).mpr (by simpa only [hg] using And.intro hN hfN)
  obtain ⟨b,hb,hdb⟩ := vertexLink_path g M N hm hn
  exact ⟨b,chains_mono (bad_vertexLink_le_good φ hφ g (by rwa [hg])) 2 hb,hdb⟩

/-- Retain Good vertices and replace each bad one by one chosen actual Good neighbor. -/
def replacementVertex (φ : Functional) (hφ : φ ≠ 0) (L : RationalLine2) : RationalLine2 := by
  classical
  exact if h : Good φ L then L else (exists_good_neighbor φ hφ L h).choose

theorem replacementVertex_of_good (φ : Functional) (hφ : φ ≠ 0) (L : RationalLine2)
    (hL : Good φ L) : replacementVertex φ hφ L = L := by
  simp only [replacementVertex,dite_eq_left hL]

theorem replacementVertex_bad_neighbor (φ : Functional) (hφ : φ ≠ 0) (L : RationalLine2)
    (hL : ¬Good φ L) : replacementVertex φ hφ L ≠ L ∧
      {L,replacementVertex φ hφ L} ∈ ambient ∧ Good φ (replacementVertex φ hφ L) := by
  simpa only [replacementVertex,dite_eq_right hL] using (exists_good_neighbor φ hφ L hL).choose_spec

theorem replacementVertex_good (φ : Functional) (hφ : φ ≠ 0) (L : RationalLine2) :
    Good φ (replacementVertex φ hφ L) := by
  by_cases hL : Good φ L
  · rwa [replacementVertex_of_good φ hφ L hL]
  · exact (replacementVertex_bad_neighbor φ hφ L hL).2.2

/-- Every ambient edge has a finite Good replacement path between its replaced endpoints. -/
theorem edge_replacement (φ : Functional) (hφ : φ ≠ 0) (L M : RationalLine2)
    (hf : {L,M} ∈ ambient) :
    ∃ b : Chain RationalLine2, b ∈ chains (good φ) 2 ∧
      boundary b = simplex [replacementVertex φ hφ M] - simplex [replacementVertex φ hφ L] := by
  by_cases he : L = M
  · subst M
    exact ⟨0,(chains (good φ) 2).zero_mem,by simp⟩
  by_cases hL : Good φ L
  · by_cases hM : Good φ M
    · refine ⟨simplex [L,M],simplex_mem_chains (good φ) [L,M] ?_,?_⟩
      · apply (allowed_good_iff φ _).mpr
        refine ⟨Or.inr ?_,?_⟩
        · simpa only [List.toFinset_cons,List.toFinset_nil,Finset.insert_empty] using hf
        · intro A hA
          rcases List.mem_cons.mp hA with rfl | hA
          · exact hL
          · simpa only [List.mem_singleton] using (List.mem_singleton.mp hA) ▸ hM
      · rw [replacementVertex_of_good φ hφ L hL,replacementVertex_of_good φ hφ M hM]
        simp only [boundary_cons,boundary_nil,map_zero,sub_zero,cons_simplex]
    · have hr := replacementVertex_bad_neighbor φ hφ M hM
      obtain ⟨b,hb,hdb⟩ := bad_neighbor_path φ hφ M L (replacementVertex φ hφ M)
        hM he hr.1 (by rwa [Finset.pair_comm]) hr.2.1
      refine ⟨b,hb,?_⟩
      rwa [replacementVertex_of_good φ hφ L hL]
  · have hM := (edge_good_or_good φ hφ L M he hf).resolve_left hL
    have hr := replacementVertex_bad_neighbor φ hφ L hL
    obtain ⟨b,hb,hdb⟩ := bad_neighbor_path φ hφ L (replacementVertex φ hφ L) M
      hL hr.1 (Ne.symm he) hr.2.1 hf
    refine ⟨b,hb,?_⟩
    rwa [replacementVertex_of_good φ hφ M hM]

/-- Good-supported chains are fixed by the replacement vertex map. -/
theorem replacement_map_good (φ : Functional) (hφ : φ ≠ 0) (n : ℕ)
    {c : Chain RationalLine2} (hc : c ∈ chains (good φ) n) :
    OrientedChainMap.map (replacementVertex φ hφ) c = c := by
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨l,_,hl,rfl⟩ := hc
    rw [OrientedChainMap.map_simplex]
    congr 1
    calc
      l.map (replacementVertex φ hφ) = l.map id := List.map_congr_left (fun L hL =>
        replacementVertex_of_good φ hφ L (((allowed_good_iff φ l).mp hl).2 L hL))
      _ = l := List.map_id l
  | zero => exact map_zero _
  | add c d hc hd ihc ihd => rw [map_add,ihc,ihd]
  | smul q c hc ih => rw [map_smul,ih]

/-- Finite span induction replaces an entire ambient edge chain while transporting its boundary. -/
theorem chain_replacement (φ : Functional) (hφ : φ ≠ 0)
    {c : Chain RationalLine2} (hc : c ∈ chains ambient 2) :
    ∃ b : Chain RationalLine2, b ∈ chains (good φ) 2 ∧
      boundary b = OrientedChainMap.map (replacementVertex φ hφ) (boundary c) := by
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨l,hlen,hl,rfl⟩ := hc
    obtain ⟨L,M,rfl⟩ := List.length_eq_two.mp hlen
    have hf : {L,M} ∈ ambient := by
      simpa only [List.toFinset_cons,List.toFinset_nil,Finset.insert_empty] using hl.resolve_left (by simp)
    obtain ⟨b,hb,hdb⟩ := edge_replacement φ hφ L M hf
    refine ⟨b,hb,?_⟩
    simpa only [boundary_cons,boundary_nil,map_zero,sub_zero,cons_simplex,map_sub,
      OrientedChainMap.map_simplex,List.map_cons,List.map_nil] using hdb
  | zero => exact ⟨0,(chains (good φ) 2).zero_mem,by simp⟩
  | add c d hc hd ihc ihd =>
    obtain ⟨b,hb,hdb⟩ := ihc
    obtain ⟨e,he,hde⟩ := ihd
    exact ⟨b+e,(chains (good φ) 2).add_mem hb he,by rw [map_add,hdb,hde,map_add,map_add]⟩
  | smul q c hc ih =>
    obtain ⟨b,hb,hdb⟩ := ih
    exact ⟨q • b,(chains (good φ) 2).smul_mem q hb,by rw [map_smul,hdb,map_smul,map_smul]⟩

end TernaryPoly.RankTwoGoodPaths
