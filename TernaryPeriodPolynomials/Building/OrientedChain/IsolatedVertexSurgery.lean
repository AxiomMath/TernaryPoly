module

public import TernaryPeriodPolynomials.Building.Good.LinkExtraction
public import TernaryPeriodPolynomials.Building.MaximalBadFaceCycle

@[expose] public section


noncomputable section
namespace TernaryPoly.OrientedIsolatedVertexSurgery
open OrientedListChains OrientedChainJoin OrientedChainProjection OrientedVertexExtraction
open OrientedBadFaceDecomposition GoodLinkExtraction MaximalBadFaceCycle
variable {V : Type*}
local instance : DecidableEq V := Classical.decEq _

/-- The full subcomplex on the retained vertices. -/
def restricted (C : PreAbstractSimplicialComplex V) (G : V → Prop) := goodLink C G ∅

theorem link_le_restricted (C : PreAbstractSimplicialComplex V) (G : V → Prop) (B : Finset V) :
    goodLink C G B ≤ restricted C G := by
  intro s hs
  obtain ⟨hne,hface,hgood⟩ := (mem_goodLink C G B s).mp hs
  apply (mem_goodLink C G ∅ s).mpr
  refine ⟨hne,?_,hgood⟩
  rw [Finset.empty_union]
  exact (C.isRelLowerSet_faces hface).2 Finset.subset_union_right hne

/-- The empty exact projection is supported entirely on retained vertices. -/
theorem empty_projection_mem (C : PreAbstractSimplicialComplex V) (G : V → Prop)
    (n : ℕ) {c : Chain V} (hc : c ∈ chains C n) :
    badFaceProjection G ∅ c ∈ chains (restricted C G) n := by
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨l,hlen,hl,rfl⟩ := hc
    by_cases he : badVertices G l = ∅
    · rw [badFaceProjection_simplex,ite_eq_left he]
      have ha : Allowed (restricted C G) l := by
        rcases hl with rfl | hl
        · exact Or.inl rfl
        · apply Or.inr
          apply (mem_goodLink C G ∅ l.toFinset).mpr
          refine ⟨(C.isRelLowerSet_faces hl).1,by simpa using hl,?_⟩
          intro a ha
          exact all_good_of_badVertices_eq_empty G l he a (List.mem_toFinset.mp ha)
      simpa only [hlen] using simplex_mem_chains _ l ha
    · rw [badFaceProjection_simplex,ite_eq_right he]
      exact (chains _ n).zero_mem
  | zero => simpa only [map_zero] using (chains (restricted C G) n).zero_mem
  | add c d hc hd ihc ihd => simpa only [map_add] using (chains _ n).add_mem ihc ihd
  | smul q c hc ih => simpa only [map_smul] using (chains _ n).smul_mem q ih

/-- A nonzero exact singleton component belongs to a removed vertex. -/
theorem not_good_of_singleton_projection_ne_zero (G : V → Prop) (a : V) (c : Chain V)
    (hne : badFaceProjection G {a} c ≠ 0) : ¬G a := by
  intro ha
  have hm : badFaceProjection G {a} = (0 : Chain V →ₗ[ℚ] Chain V) := by
    apply chain_ext
    intro l
    have he : badVertices G l ≠ {a} := by
      intro he
      have hmem : a ∈ badVertices G l := he.symm ▸ Finset.mem_singleton_self a
      exact (BadFaceContraction.mem_badVertices G l a).mp hmem |>.2 ha
    simp only [badFaceProjection_simplex,ite_eq_right he,LinearMap.zero_apply]
  exact hne (by rw [hm,LinearMap.zero_apply])

/-- A surviving singleton component is an actual vertex of the ambient complex. -/
theorem singleton_mem_of_projection_ne_zero (C : PreAbstractSimplicialComplex V)
    (G : V → Prop) (a : V) (n : ℕ) {c : Chain V} (hc : c ∈ chains C n)
    (hne : badFaceProjection G {a} c ≠ 0) : {a} ∈ C := by
  by_contra hnot
  apply hne
  clear hne
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨l,_,hl,rfl⟩ := hc
    have he : badVertices G l ≠ {a} := by
      intro he
      have hm : a ∈ l := ((BadFaceContraction.mem_badVertices G l a).mp
        (he.symm ▸ Finset.mem_singleton_self a)).1
      rcases hl with rfl | hl
      · simp at hm
      · exact hnot ((C.isRelLowerSet_faces hl).2
          (Finset.singleton_subset_iff.mpr (List.mem_toFinset.mpr hm)) (by simp))
    simp only [badFaceProjection_simplex,ite_eq_right he]
  | zero => exact map_zero _
  | add c d hc hd ihc ihd => simp only [map_add,ihc,ihd,add_zero]
  | smul q c hc ih => simp only [map_smul,ih,smul_zero]

/-- Coning a positive-degree link chain gives an actual ambient chain. -/
theorem cons_link_mem (C : PreAbstractSimplicialComplex V) (G : V → Prop)
    (a : V) (n : ℕ) {b : Chain V} (hb : b ∈ chains (goodLink C G {a}) (n+1)) :
    cons a b ∈ chains C (n+2) := by
  change b ∈ (chains C (n+2)).comap (cons a)
  apply (Submodule.span_le.mpr ?_) hb
  rintro _ ⟨l,hlen,hl,rfl⟩
  change cons a (simplex l) ∈ chains C (n+2)
  rw [cons_simplex]
  have hface : l.toFinset ∈ goodLink C G {a} := hl.resolve_left (by intro h; simp [h] at hlen)
  have ha : Allowed C (a::l) := by
    apply Or.inr
    convert ((mem_goodLink C G {a} l.toFinset).mp hface).2.1 using 1
    ext x
    simp
  simpa only [List.length_cons,hlen,Nat.add_assoc] using simplex_mem_chains C (a::l) ha

/-- The precise local hypothesis for removing isolated vertices in a two-cycle. -/
def LinkFilling (C : PreAbstractSimplicialComplex V) (G : V → Prop) : Prop :=
  ∀ a : V, {a} ∈ C → ¬G a → ∀ u : Chain V, u ∈ chains (goodLink C G {a}) 2 → boundary u = 0 →
    ∃ b : Chain V, b ∈ chains (goodLink C G {a}) 3 ∧ boundary b = u

/-- Each exact component has a retained replacement with an explicit ambient filling difference. -/
theorem component_replacement (C : PreAbstractSimplicialComplex V) (G : V → Prop)
    (hfill : LinkFilling C G) {c : Chain V} (hc : c ∈ chains C 3) (hd : boundary c = 0)
    (hmax : ∀ s : Finset V, 1 < s.card → badFaceProjection G s c = 0) (s : Finset V) :
    ∃ t r : Chain V, t ∈ chains C 4 ∧ r ∈ chains (restricted C G) 3 ∧
      badFaceProjection G s c = boundary t + r := by
  by_cases hz : badFaceProjection G s c = 0
  · exact ⟨0,0,(chains C 4).zero_mem,(chains _ 3).zero_mem,by simp [hz]⟩
  by_cases he : s = ∅
  · subst s
    exact ⟨0,badFaceProjection G ∅ c,(chains C 4).zero_mem,
      empty_projection_mem C G 3 hc,by simp⟩
  have hs : s.card = 1 := by
    have hp : 0 < s.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr he)
    by_contra hn
    exact hz (hmax s (by omega))
  obtain ⟨a,rfl⟩ := Finset.card_eq_one.mp hs
  have ha := not_good_of_singleton_projection_ne_zero G a c hz
  have hbad : ∀ v ∈ ([a] : List V), ¬G v := by
    intro v hv
    simpa only [List.mem_singleton] using (List.mem_singleton.mp hv) ▸ ha
  have hset : ([a] : List V).toFinset = {a} := by simp
  have hu := extract_badFaceProjection_mem_goodLink C G [a] (by simp) hbad 2 hc
  have hdu := boundary_extract_projection_eq_zero G [a] (by simp) (by simp) hbad c
    (by simpa using hmax) (by simp [hd])
  rw [hset] at hu hdu
  obtain ⟨b,hb,hdb⟩ := hfill a (singleton_mem_of_projection_ne_zero C G a 3 hc hz) ha _ hu hdu
  refine ⟨-cons a b,b,(chains C 4).neg_mem (cons_link_mem C G a 2 hb),
    chains_mono (link_le_restricted C G {a}) 3 hb,?_⟩
  have hfactor := badFaceProjection_eq_join_extract G [a] (by simp) c
  rw [hset] at hfactor
  simp only [join_simplex_left,prependList,LinearMap.comp_apply,LinearMap.id_apply] at hfactor
  rw [map_neg,boundary_cons_chain,hdb,hfactor]
  abel

/-- Finite exact decomposition removes all isolated bad vertices of a two-cycle. -/
theorem eliminate_isolated_vertices (C : PreAbstractSimplicialComplex V) (G : V → Prop)
    (hfill : LinkFilling C G) {c : Chain V} (hc : c ∈ chains C 3) (hd : boundary c = 0)
    (hmax : ∀ s : Finset V, 1 < s.card → badFaceProjection G s c = 0) :
    ∃ t r : Chain V, t ∈ chains C 4 ∧ r ∈ chains (restricted C G) 3 ∧
      c = boundary t + r ∧ boundary r = 0 := by
  obtain ⟨S,hS,_⟩ := exists_badFace_decomposition G c
  choose t r ht hr he using component_replacement C G hfill hc hd hmax
  have hsum : c = boundary (∑ s ∈ S,t s) + ∑ s ∈ S,r s := by
    rw [map_sum,← Finset.sum_add_distrib]
    simp_rw [← he]
    exact hS.symm
  refine ⟨∑ s ∈ S,t s,∑ s ∈ S,r s,(chains C 4).sum_mem (fun s _ => ht s),
    (chains (restricted C G) 3).sum_mem (fun s _ => hr s),hsum,?_⟩
  have h := congrArg boundary hsum
  rw [hd,map_add,boundary_squared,zero_add] at h
  exact h.symm

end TernaryPoly.OrientedIsolatedVertexSurgery
