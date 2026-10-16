module

public import TernaryPeriodPolynomials.Building.OrientedChain.VertexExtraction
public import TernaryPeriodPolynomials.Building.OrientedChain.ChainProjection

@[expose] public section


noncomputable section
namespace TernaryPoly.BadFaceContraction
open OrientedListChains OrientedChainJoin OrientedChainContraction
open OrientedVertexExtraction OrientedChainProjection
variable {V : Type*}
local instance : DecidableEq V := Classical.decEq V

/-- The exact bad-vertex predicate is literal membership together with badness. -/
theorem mem_badVertices (G : V → Prop) (l : List V) (a : V) :
    a ∈ badVertices G l ↔ a ∈ l ∧ ¬G a := by
  classical
  simp only [badVertices,Finset.mem_filter,List.mem_toFinset]

/-- Deleting one vertex from a nonrepeated list deletes it from its exact bad face. -/
theorem badVertices_erase (G : V → Prop) (l : List V) (hl : l.Nodup) (a : V) :
    badVertices G (l.erase a) = (badVertices G l).erase a := by
  classical
  ext b
  simp only [mem_badVertices,hl.mem_erase_iff,Finset.mem_erase,and_assoc]

/-- A vertex contraction of a nonrepeated simplex containing it is its erased simplex up to sign. -/
theorem atVertex_simplex_eq_sign_erase (a : V) (l : List V)
    (hl : l.Nodup) (ha : a ∈ l) :
    ∃ e : ℤ, (e = 1 ∨ e = -1) ∧
      atVertex a (simplex l) = (e : ℚ) • simplex (l.erase a) := by
  classical
  induction l with
  | nil => exact (List.not_mem_nil ha).elim
  | cons b l ih =>
    obtain ⟨hb,hl⟩ := List.nodup_cons.mp hl
    by_cases hba : b = a
    · subst b
      refine ⟨1,Or.inl rfl,?_⟩
      rw [← cons_simplex,atVertex_cons_self,atVertex_simplex_of_not_mem a l hb,map_zero,sub_zero]
      simp
    · have hal : a ∈ l := (List.mem_cons.mp ha).resolve_left (Ne.symm hba)
      obtain ⟨e,he,hs⟩ := ih hl hal
      refine ⟨-e,?_,?_⟩
      · rcases he with rfl | rfl <;> simp
      · rw [← cons_simplex,atVertex_cons_ne a b hba,hs,map_smul,cons_simplex]
        simp [hba]

/-- If the contracted bad vertex belongs to both exact faces, their erased faces agree exactly together. -/
theorem badVertices_erase_eq_iff (G : V → Prop) (s : Finset V) (a : V)
    (has : a ∈ s) (hbad : ¬G a) (l : List V) (hl : l.Nodup) (ha : a ∈ l) :
    badVertices G (l.erase a) = s.erase a ↔ badVertices G l = s := by
  classical
  rw [badVertices_erase G l hl a]
  have hab : a ∈ badVertices G l := (mem_badVertices G l a).mpr ⟨ha,hbad⟩
  constructor
  · intro he
    calc
      badVertices G l = insert a ((badVertices G l).erase a) := (Finset.insert_erase hab).symm
      _ = insert a (s.erase a) := congrArg (insert a) he
      _ = s := Finset.insert_erase has
  · exact congrArg (fun t : Finset V => t.erase a)

/-- Exact bad-face projections commute with deleting a bad vertex, with that vertex erased from the index. -/
theorem atVertex_badFaceProjection (G : V → Prop) (s : Finset V) (a : V)
    (has : a ∈ s) (hbad : ¬G a) (c : Chain V) :
    atVertex a (badFaceProjection G s c) =
      badFaceProjection G (s.erase a) (atVertex a c) := by
  classical
  have he : (atVertex a).comp (badFaceProjection G s) =
      (badFaceProjection G (s.erase a)).comp (atVertex a) := by
    apply chain_ext
    intro l
    change atVertex a (badFaceProjection G s (simplex l)) =
      badFaceProjection G (s.erase a) (atVertex a (simplex l))
    by_cases hl : l.Nodup
    · by_cases ha : a ∈ l
      · obtain ⟨e,_,hs⟩ := atVertex_simplex_eq_sign_erase a l hl ha
        have herase := badVertices_erase_eq_iff G s a has hbad l hl ha
        by_cases hls : badVertices G l = s
        · rw [badFaceProjection_simplex,ite_eq_left hls,hs,map_smul,
            badFaceProjection_simplex,ite_eq_left (herase.mpr hls)]
        · rw [badFaceProjection_simplex,ite_eq_right hls,map_zero,hs,map_smul,
            badFaceProjection_simplex,ite_eq_right (fun h => hls (herase.mp h)),smul_zero]
      · have hz := atVertex_simplex_of_not_mem a l ha
        by_cases hls : badVertices G l = s <;> simp [hls,hz]
    · rw [simplex_eq_zero_of_not_nodup l hl]
      simp
  exact LinearMap.congr_fun he c

/-- A bad vertex outside the exact projected face has zero contraction. -/
theorem atVertex_badFaceProjection_eq_zero (G : V → Prop) (s : Finset V) (a : V)
    (has : a ∉ s) (hbad : ¬G a) (c : Chain V) :
    atVertex a (badFaceProjection G s c) = 0 := by
  classical
  have he : (atVertex a).comp (badFaceProjection G s) = (0 : Chain V →ₗ[ℚ] Chain V) := by
    apply chain_ext
    intro l
    change atVertex a (badFaceProjection G s (simplex l)) = 0
    by_cases hls : badVertices G l = s
    · have ha : a ∉ l := by
        intro hal
        have hab := (mem_badVertices G l a).mpr ⟨hal,hbad⟩
        exact has (hls ▸ hab)
      rw [badFaceProjection_simplex,ite_eq_left hls,atVertex_simplex_of_not_mem a l ha]
    · simp [hls]
  exact LinearMap.congr_fun he c

/-- Deleting a listed bad vertex preserves exact support on the erased bad face. -/
theorem atVertex_projection_has_exact_support (G : V → Prop) (s : Finset V) (a : V)
    (has : a ∈ s) (hbad : ¬G a) (c : Chain V) :
    badFaceProjection G (s.erase a) (atVertex a (badFaceProjection G s c)) =
      atVertex a (badFaceProjection G s c) := by
  rw [atVertex_badFaceProjection G s a has hbad]
  exact filter_idempotent _ (fun h => by rw [badVertices_perm G h]) _

/-- On a chain with exact bad face s, contraction has exact bad face s minus the contracted vertex. -/
theorem atVertex_has_exact_support (G : V → Prop) (s : Finset V) (a : V)
    (has : a ∈ s) (hbad : ¬G a) (c : Chain V) (hc : badFaceProjection G s c = c) :
    badFaceProjection G (s.erase a) (atVertex a c) = atVertex a c := by
  have he := atVertex_badFaceProjection G s a has hbad c
  rw [hc] at he
  exact he.symm

/-- Extracting a nonrepeated all-bad list removes its entire exact bad face. -/
theorem extract_badFaceProjection (G : V → Prop) (B : List V) (hB : B.Nodup)
    (hbad : ∀ a ∈ B, ¬G a) (c : Chain V) :
    extract B (badFaceProjection G B.toFinset c) =
      badFaceProjection G ∅ (extract B c) := by
  classical
  induction B generalizing c with
  | nil => rfl
  | cons a B ih =>
    obtain ⟨ha,hB⟩ := List.nodup_cons.mp hB
    change extract B (atVertex a (badFaceProjection G (a :: B).toFinset c)) =
      badFaceProjection G ∅ (extract B (atVertex a c))
    rw [atVertex_badFaceProjection G (a :: B).toFinset a (by simp)
      (hbad a List.mem_cons_self)]
    have hs : (a :: B).toFinset.erase a = B.toFinset := by simp [ha]
    rw [hs]
    exact ih hB (fun b hb => hbad b (List.mem_cons_of_mem a hb)) (atVertex a c)

/-- The extracted coefficient of an exact all-bad face has actual Good support. -/
theorem extract_projection_has_good_support (G : V → Prop) (B : List V) (hB : B.Nodup)
    (hbad : ∀ a ∈ B, ¬G a) (c : Chain V) :
    badFaceProjection G ∅ (extract B (badFaceProjection G B.toFinset c)) =
      extract B (badFaceProjection G B.toFinset c) := by
  rw [extract_badFaceProjection G B hB hbad]
  exact filter_idempotent _ (fun h => by rw [badVertices_perm G h]) _

/-- Exact input support suffices to ensure all-Good output support after extracting its bad face. -/
theorem extract_has_good_support (G : V → Prop) (B : List V) (hB : B.Nodup)
    (hbad : ∀ a ∈ B, ¬G a) (c : Chain V) (hc : badFaceProjection G B.toFinset c = c) :
    badFaceProjection G ∅ (extract B c) = extract B c := by
  have he := extract_badFaceProjection G B hB hbad c
  rw [hc] at he
  exact he.symm

end TernaryPoly.BadFaceContraction
