module

public import TernaryPeriodPolynomials.Building.OrientedChain.BadFaceDecomposition
public import TernaryPeriodPolynomials.Building.Good.LinkExtraction

@[expose] public section


noncomputable section
namespace TernaryPoly.PositiveChainSeparation
open OrientedListChains OrientedChainJoin OrientedChainContraction
open OrientedVertexExtraction OrientedChainProjection OrientedBadFaceDecomposition
open BadFaceContraction GoodLinkExtraction
variable {V : Type*}
local instance : DecidableEq V := Classical.decEq V

/-- Prefixing after coordinate contraction is the literal vertex-membership projection. -/
theorem cons_atVertex_simplex (a : V) (l : List V) :
    cons a (atVertex a (simplex l)) = if a ∈ l then simplex l else 0 := by
  classical
  by_cases ha : a ∈ l
  · rw [ite_eq_left ha]
    exact cons_atVertex_of_cons_eq_zero a (simplex l) (cons_simplex_eq_zero_of_mem a l ha)
  · rw [ite_eq_right ha,atVertex_simplex_of_not_mem a l ha,map_zero]

/-- A finite vertex set containing a simplex gives the exact Euler identity in the quotient. -/
theorem euler_simplex (l : List V) (S : Finset V) (hS : l.toFinset ⊆ S) :
    (∑ a ∈ S, cons a (atVertex a (simplex l))) = (l.length : ℚ) • simplex l := by
  classical
  by_cases hl : l.Nodup
  · have he : (∑ a ∈ l.toFinset, cons a (atVertex a (simplex l))) =
        ∑ a ∈ S, cons a (atVertex a (simplex l)) := by
      apply Finset.sum_subset hS
      intro a ha hnot
      rw [atVertex_simplex_of_not_mem a l (fun h => hnot (List.mem_toFinset.mpr h)),map_zero]
    rw [← he]
    calc
      _ = ∑ a ∈ l.toFinset, simplex l := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [cons_atVertex_simplex,ite_eq_left (List.mem_toFinset.mp ha)]
      _ = (l.length : ℚ) • simplex l := by
        rw [Finset.sum_const,List.toFinset_card_of_nodup hl,Nat.cast_smul_eq_nsmul]
  · rw [simplex_eq_zero_of_not_nodup l hl]
    simp only [map_zero,Finset.sum_const_zero,smul_zero]

/-- Span induction supplies a finite representative consisting only of supported homogeneous simplices. -/
theorem exists_supported_representative (C : PreAbstractSimplicialComplex V) (n : ℕ)
    {c : Chain V} (hc : c ∈ chains C n) :
    ∃ r : Raw V, (∀ l ∈ r.support, l.length = n ∧ Allowed C l) ∧ (relations V).mkQ r = c := by
  classical
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨l,hlen,hl,rfl⟩ := hc
    refine ⟨rawSimplex l,?_,rfl⟩
    intro m hm
    have he : m = l := by simpa [rawSimplex] using hm
    subst m
    exact ⟨hlen,hl⟩
  | zero => exact ⟨0,by simp,by simp⟩
  | add c d hc hd ihc ihd =>
    obtain ⟨r,hr,hqr⟩ := ihc
    obtain ⟨s,hs,hqs⟩ := ihd
    refine ⟨r+s,?_,by rw [map_add,hqr,hqs]⟩
    intro l hl
    by_cases hrl : r l = 0
    · apply hs l
      apply Finsupp.mem_support_iff.mpr
      have h := Finsupp.mem_support_iff.mp hl
      simpa only [Finsupp.add_apply,hrl,zero_add] using h
    · exact hr l (Finsupp.mem_support_iff.mpr hrl)
  | smul q c hc ih =>
    obtain ⟨r,hr,hqr⟩ := ih
    refine ⟨q • r,?_,by rw [map_smul,hqr]⟩
    intro l hl
    apply hr l
    apply Finsupp.mem_support_iff.mpr
    intro h
    have hne := Finsupp.mem_support_iff.mp hl
    apply hne
    simp only [Finsupp.smul_apply,h,smul_zero]

/-- The homogeneous finite representative satisfies Euler's identity on any covering vertex set. -/
theorem euler_representative (n : ℕ) (r : Raw V)
    (hr : ∀ l ∈ r.support, l.length = n) (S : Finset V)
    (hS : ∀ l ∈ r.support, l.toFinset ⊆ S) :
    (∑ a ∈ S, cons a (atVertex a ((relations V).mkQ r))) =
      (n : ℚ) • (relations V).mkQ r := by
  rw [mkQ_expansion]
  simp only [map_sum,map_smul]
  rw [Finset.sum_comm]
  simp only [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro l hl
  rw [← Finset.smul_sum,euler_simplex l S (hS l hl),hr l hl,smul_comm]

/-- Every supported homogeneous chain admits a finite Euler identity, independently of any chain basis. -/
theorem exists_euler_identity (C : PreAbstractSimplicialComplex V) (n : ℕ)
    {c : Chain V} (hc : c ∈ chains C n) :
    ∃ S : Finset V, (∑ a ∈ S, cons a (atVertex a c)) = (n : ℚ) • c := by
  classical
  obtain ⟨r,hr,rfl⟩ := exists_supported_representative C n hc
  refine ⟨r.support.biUnion List.toFinset,euler_representative n r (fun l hl => (hr l hl).1) _ ?_⟩
  intro l hl a ha
  exact Finset.mem_biUnion.mpr ⟨l,hl,ha⟩

/-- Positive-degree actual chains are separated by their coordinate vertex contractions. -/
theorem eq_zero_of_atVertex_eq_zero (C : PreAbstractSimplicialComplex V) (n : ℕ)
    (hn : 0 < n) {c : Chain V} (hc : c ∈ chains C n)
    (hzero : ∀ a : V, atVertex a c = 0) : c = 0 := by
  obtain ⟨S,hS⟩ := exists_euler_identity C n hc
  have he : (n : ℚ) • c = 0 := by
    rw [← hS]
    simp only [hzero,map_zero,Finset.sum_const_zero]
  exact (smul_eq_zero.mp he).resolve_left (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn))

/-- For the complement-of-a-vertex predicate, the singleton exact bad face means literal containment. -/
theorem badVertices_ne_singleton_iff (a : V) (l : List V) :
    badVertices (fun b => b ≠ a) l = {a} ↔ a ∈ l := by
  classical
  constructor
  · intro h
    have hm : a ∈ badVertices (fun b => b ≠ a) l := by rw [h]; exact Finset.mem_singleton_self a
    exact (mem_badVertices _ _ _).mp hm |>.1
  · intro ha
    ext b
    simp only [mem_badVertices,not_not,Finset.mem_singleton]
    constructor
    · exact And.right
    · intro hb
      exact ⟨by simpa only [hb] using ha,hb⟩

/-- Prefixing after contraction is exactly the singleton bad-face projection for the complementary predicate. -/
theorem cons_atVertex_eq_projection (a : V) (c : Chain V) :
    cons a (atVertex a c) = badFaceProjection (fun b => b ≠ a) {a} c := by
  have he : (cons a).comp (atVertex a) = badFaceProjection (fun b => b ≠ a) {a} := by
    apply chain_ext
    intro l
    change cons a (atVertex a (simplex l)) = _
    rw [cons_atVertex_simplex,badFaceProjection_simplex]
    have h := badVertices_ne_singleton_iff a l
    split_ifs with ha hb hb
    · rfl
    · exact (hb (h.mpr ha)).elim
    · exact (ha (h.mp hb)).elim
    · rfl
  exact LinearMap.congr_fun he c

/-- Contraction ignores the part of a chain not containing its vertex. -/
theorem atVertex_projection (a : V) (c : Chain V) :
    atVertex a (badFaceProjection (fun b => b ≠ a) {a} c) = atVertex a c := by
  rw [← cons_atVertex_eq_projection,atVertex_cons_self]
  have h : atVertex a (atVertex a c) = 0 := contraction_squared (vertexWeight a) c
  rw [h,map_zero,sub_zero]

/-- Actual coordinate contraction belongs to the actual vertex link, with the correct degree. -/
theorem atVertex_mem_link (C : PreAbstractSimplicialComplex V) (a : V) (n : ℕ)
    {c : Chain V} (hc : c ∈ chains C (n+1)) :
    atVertex a c ∈ chains (goodLink C (fun b => b ≠ a) {a}) n := by
  classical
  have he := extract_badFaceProjection_mem_goodLink C (fun b => b ≠ a) [a]
    (by simp) (by simp) n hc
  have hs : ([a] : List V).toFinset = {a} := by ext b; simp
  simpa only [hs,extract,LinearMap.comp_apply,LinearMap.id_apply,atVertex_projection] using he

/-- The contraction of an actual cycle is an actual cycle in its vertex link. -/
theorem atVertex_link_cycle (C : PreAbstractSimplicialComplex V) (a : V) (n : ℕ)
    {c : Chain V} (hc : c ∈ chains C (n+1)) (hd : boundary c = 0) :
    atVertex a c ∈ chains (goodLink C (fun b => b ≠ a) {a}) n ∧
      boundary (atVertex a c) = 0 := by
  refine ⟨atVertex_mem_link C a n hc,?_⟩
  have he := contraction_boundary (vertexWeight a) c
  rw [hd,map_zero] at he
  exact neg_eq_zero.mp he.symm

/-- Vanishing of all vertex-link cycles forces vanishing of the next-degree actual cycles. -/
theorem cycle_eq_zero_of_vertex_links (C : PreAbstractSimplicialComplex V) (n : ℕ)
    (hlinks : ∀ a : V, ∀ z : Chain V,
      z ∈ chains (goodLink C (fun b => b ≠ a) {a}) n → boundary z = 0 → z = 0)
    {c : Chain V} (hc : c ∈ chains C (n+1)) (hd : boundary c = 0) : c = 0 := by
  apply eq_zero_of_atVertex_eq_zero C (n+1) (Nat.zero_lt_succ n) hc
  intro a
  obtain ⟨hmem,hcycle⟩ := atVertex_link_cycle C a n hc hd
  exact hlinks a (atVertex a c) hmem hcycle

/-- Actual boundary injectivity one degree higher follows from vanishing cycles in every vertex link. -/
theorem boundary_injective_of_vertex_links (C : PreAbstractSimplicialComplex V) (n : ℕ)
    (hlinks : ∀ a : V, ∀ z : Chain V,
      z ∈ chains (goodLink C (fun b => b ≠ a) {a}) n → boundary z = 0 → z = 0)
    {c d : Chain V} (hc : c ∈ chains C (n+1)) (hd : d ∈ chains C (n+1))
    (he : boundary c = boundary d) : c = d := by
  apply sub_eq_zero.mp
  apply cycle_eq_zero_of_vertex_links C n hlinks ((chains C (n+1)).sub_mem hc hd)
  rw [map_sub,he,sub_self]

end TernaryPoly.PositiveChainSeparation
