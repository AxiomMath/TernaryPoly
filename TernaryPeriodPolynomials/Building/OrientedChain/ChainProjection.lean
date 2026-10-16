module

public import TernaryPeriodPolynomials.Building.OrientedChain.ChainJoin

@[expose] public section

noncomputable section
namespace TernaryPoly.OrientedChainProjection
open OrientedListChains OrientedChainJoin
variable {V : Type*}
local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- A list property independent of the ordering of its vertices. -/
def PermInvariant (P : List V → Prop) : Prop :=
  ∀ {l m : List V}, l.Perm m → (P l ↔ P m)

/-- The literal coordinate projection on finite free list chains. -/
def rawFilter (P : List V → Prop) : Raw V →ₗ[ℚ] Raw V := by
  classical
  exact Finsupp.lsum ℚ (fun l => if P l then Finsupp.lsingle l else 0)

@[simp] theorem rawFilter_simplex (P : List V → Prop) (l : List V) :
    rawFilter P (rawSimplex l) = if P l then rawSimplex l else 0 := by
  classical
  by_cases h : P l <;> simp [rawFilter,rawSimplex,h]

theorem rawFilter_rawCons (P : List V → Prop) (a : V) (c : Raw V) :
    rawFilter P (rawCons a c) = rawCons a (rawFilter (fun l => P (a :: l)) c) := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add,hc,hd]
  | single l q =>
    have hq : Finsupp.single l q = q • rawSimplex l := by simp [rawSimplex]
    by_cases h : P (a :: l) <;>
      simp only [hq,map_smul,rawCons_simplex,rawFilter_simplex,h,ite_true,ite_false,map_zero]

theorem rawFilter_relation {c : Raw V} (hc : c ∈ relations V) :
    ∀ P : List V → Prop, PermInvariant P → rawFilter P c ∈ relations V := by
  classical
  induction hc with
  | swap a b l =>
    intro P hp
    have he : P (a :: b :: l) ↔ P (b :: a :: l) := hp (List.Perm.swap b a l)
    by_cases h : P (a :: b :: l)
    · simp only [map_add,rawFilter_simplex,h,he.mp h,ite_true]
      exact Relation.swap a b l
    · have hn : ¬P (b :: a :: l) := fun hb => h (he.mpr hb)
      simp only [map_add,rawFilter_simplex,h,hn,ite_false,add_zero]
      exact (relations V).zero_mem
  | cons a hc ih =>
    intro P hp
    rw [rawFilter_rawCons]
    exact rawCons_relation a (ih (fun l => P (a :: l)) (fun h => hp (h.cons a)))
  | zero => intro P hp; simp
  | add hc hd ihc ihd =>
    intro P hp
    simpa only [map_add] using (relations V).add_mem (ihc P hp) (ihd P hp)
  | smul q hc ih =>
    intro P hp
    simpa only [map_smul] using (relations V).smul_mem q (ih P hp)

/-- An ordering-independent simplex projection on actual oriented chains. -/
def filter (P : List V → Prop) (hp : PermInvariant P) : Chain V →ₗ[ℚ] Chain V :=
  (relations V).mapQ (relations V) (rawFilter P) (fun _ hc => rawFilter_relation hc P hp)

@[simp] theorem filter_simplex (P : List V → Prop) (hp : PermInvariant P) (l : List V) :
    filter P hp (simplex l) = if P l then simplex l else 0 := by
  classical
  change (relations V).mkQ (rawFilter P (rawSimplex l)) = _
  rw [rawFilter_simplex]
  split <;> simp_all [simplex]

theorem filter_idempotent (P : List V → Prop) (hp : PermInvariant P) (c : Chain V) :
    filter P hp (filter P hp c) = filter P hp c := by
  have he : (filter P hp).comp (filter P hp) = filter P hp := by
    apply chain_ext
    intro l
    by_cases h : P l <;> simp [h]
  exact LinearMap.congr_fun he c

theorem filter_mem_chains (P : List V → Prop) (hp : PermInvariant P)
    (C : PreAbstractSimplicialComplex V) (n : ℕ) {c : Chain V} (hc : c ∈ chains C n) :
    filter P hp c ∈ chains C n := by
  classical
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨l,hlen,hl,rfl⟩ := hc
    by_cases h : P l
    · rw [filter_simplex,ite_eq_left h]
      simpa only [hlen] using simplex_mem_chains C l hl
    · rw [filter_simplex,ite_eq_right h]
      exact (chains C n).zero_mem
  | zero => simp
  | add c d hc hd ihc ihd => simpa only [map_add] using (chains C n).add_mem ihc ihd
  | smul q c hc ih => simpa only [map_smul] using (chains C n).smul_mem q ih

/-- The exact bad face of a displayed simplex. -/
def badVertices (G : V → Prop) (l : List V) : Finset V := by
  classical
  exact l.toFinset.filter (fun v => ¬G v)

theorem badVertices_perm (G : V → Prop) {l m : List V} (h : l.Perm m) :
    badVertices G l = badVertices G m := by
  classical
  ext v
  simp only [badVertices,Finset.mem_filter,List.mem_toFinset,h.mem_iff]

/-- Project onto the summand with precisely the specified bad face. -/
def badFaceProjection (G : V → Prop) (s : Finset V) : Chain V →ₗ[ℚ] Chain V :=
  filter (fun l => badVertices G l = s) (fun h => by dsimp only; rw [badVertices_perm G h])

@[simp] theorem badFaceProjection_simplex (G : V → Prop) (s : Finset V) (l : List V) :
    badFaceProjection G s (simplex l) = if badVertices G l = s then simplex l else 0 := by
  have he := filter_simplex (fun m => badVertices G m = s)
    (fun h => by dsimp only; rw [badVertices_perm G h]) l
  convert he using 1
  · rfl
  · split_ifs <;> rfl

/-- Distinct bad-face summands are disjoint, before any topological assertions. -/
theorem badFaceProjection_orthogonal (G : V → Prop) (s t : Finset V) (hst : s ≠ t)
    (c : Chain V) : badFaceProjection G s (badFaceProjection G t c) = 0 := by
  have he : (badFaceProjection G s).comp (badFaceProjection G t) =
      (0 : Chain V →ₗ[ℚ] Chain V) := by
    apply chain_ext
    intro l
    by_cases ht : badVertices G l = t
    · simp [ht,Ne.symm hst]
    · simp [ht]
  exact LinearMap.congr_fun he c

/-- The number of distinct bad vertices. -/
def badCount (G : V → Prop) (l : List V) : ℕ := (badVertices G l).card

theorem badCount_le_length (G : V → Prop) (l : List V) : badCount G l ≤ l.length := by
  classical
  exact (Finset.card_filter_le _ _).trans (List.toFinset_card_le l)

def badCountProjection (G : V → Prop) (r : ℕ) : Chain V →ₗ[ℚ] Chain V :=
  filter (fun l => badCount G l = r)
    (fun h => by dsimp only; unfold badCount; rw [badVertices_perm G h])

@[simp] theorem badCountProjection_simplex (G : V → Prop) (r : ℕ) (l : List V) :
    badCountProjection G r (simplex l) = if badCount G l = r then simplex l else 0 := by
  have he := filter_simplex (fun m => badCount G m = r)
    (fun h => by dsimp only; unfold badCount; rw [badVertices_perm G h]) l
  convert he using 1
  · rfl
  · split_ifs <;> rfl

/-- Every finite n-vertex chain is the sum of its exact bad-count pieces. -/
theorem sum_badCountProjection (G : V → Prop) (C : PreAbstractSimplicialComplex V)
    (n : ℕ) {c : Chain V} (hc : c ∈ chains C n) :
    ∑ r ∈ Finset.range (n+1), badCountProjection G r c = c := by
  classical
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨l,hlen,_,rfl⟩ := hc
    have hb : badCount G l < n+1 := Nat.lt_succ_of_le (hlen ▸ badCount_le_length G l)
    simp [hb]
  | zero => simp
  | add c d hc hd ihc ihd => simp only [map_add,Finset.sum_add_distrib,ihc,ihd]
  | smul q c hc ih => simp only [map_smul,← Finset.smul_sum,ih]

end TernaryPoly.OrientedChainProjection
