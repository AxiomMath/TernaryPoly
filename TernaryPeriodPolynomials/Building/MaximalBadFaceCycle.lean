module

public import TernaryPeriodPolynomials.Building.BadFace.Contraction
public import TernaryPeriodPolynomials.Building.OrientedChain.BadFaceDecomposition

@[expose] public section


noncomputable section
namespace TernaryPoly.MaximalBadFaceCycle
open OrientedListChains OrientedChainProjection OrientedVertexExtraction
open BadFaceContraction OrientedBadFaceDecomposition
variable {V : Type*}
local instance : DecidableEq V := Classical.decEq V

/-- Extraction vanishes if the projected bad face omits any extracted bad vertex. -/
theorem extract_projection_eq_zero_of_not_subset (G : V → Prop) (B : List V)
    (hbad : ∀ a ∈ B, ¬G a) (s : Finset V) (h : ¬B.toFinset ⊆ s) (c : Chain V) :
    extract B (badFaceProjection G s c) = 0 := by
  classical
  induction B generalizing s c with
  | nil => exact (h (by simp)).elim
  | cons a B ih =>
    change extract B (atVertex a (badFaceProjection G s c)) = 0
    by_cases ha : a ∈ s
    · rw [atVertex_badFaceProjection G s a ha (hbad a List.mem_cons_self)]
      apply ih (fun b hb => hbad b (List.mem_cons_of_mem a hb)) (s.erase a)
      intro hs
      apply h
      intro b hb
      rcases List.mem_cons.mp (List.mem_toFinset.mp hb) with rfl | hb
      · exact ha
      · exact Finset.mem_of_mem_erase (hs (List.mem_toFinset.mpr hb))
    · rw [atVertex_badFaceProjection_eq_zero G s a ha (hbad a List.mem_cons_self),map_zero]

/-- With no larger bad faces, extraction sees just its own exact bad-face summand. -/
theorem extract_eq_extract_projection (G : V → Prop) (B : List V) (hB : B.Nodup)
    (hbad : ∀ a ∈ B, ¬G a) (c : Chain V)
    (hmax : ∀ s : Finset V, B.length < s.card → badFaceProjection G s c = 0) :
    extract B c = extract B (badFaceProjection G B.toFinset c) := by
  classical
  obtain ⟨S,hS,_⟩ := exists_badFace_decomposition G c
  have hz (s : Finset V) (hne : s ≠ B.toFinset) :
      extract B (badFaceProjection G s c) = 0 := by
    by_cases hbig : B.length < s.card
    · rw [hmax s hbig,map_zero]
    · apply extract_projection_eq_zero_of_not_subset G B hbad s
      intro hsub
      apply hne
      apply (Finset.eq_of_subset_of_card_le hsub ?_).symm
      simpa only [List.toFinset_card_of_nodup hB] using Nat.le_of_not_gt hbig
  calc
    extract B c = ∑ s ∈ S, extract B (badFaceProjection G s c) := by rw [← map_sum,hS]
    _ = ∑ s ∈ S, extract B (badFaceProjection G B.toFinset (badFaceProjection G s c)) := by
      apply Finset.sum_congr rfl
      intro s hs
      by_cases he : s = B.toFinset
      · subst s
        rw [show badFaceProjection G B.toFinset (badFaceProjection G B.toFinset c) =
          badFaceProjection G B.toFinset c from
            filter_idempotent _ (fun h => by rw [badVertices_perm G h]) c]
      · rw [hz s he,badFaceProjection_orthogonal G B.toFinset s (Ne.symm he),map_zero]
    _ = extract B (badFaceProjection G B.toFinset c) := by rw [← map_sum,← map_sum,hS]

/-- A nonempty maximal bad face of a chain with Good boundary has a cycle as link coefficient. -/
theorem boundary_extract_projection_eq_zero (G : V → Prop) (B : List V)
    (hB : B.Nodup) (hBne : B ≠ []) (hbad : ∀ a ∈ B, ¬G a) (c : Chain V)
    (hmax : ∀ s : Finset V, B.length < s.card → badFaceProjection G s c = 0)
    (hboundary : badFaceProjection G ∅ (boundary c) = boundary c) :
    boundary (extract B (badFaceProjection G B.toFinset c)) = 0 := by
  have hzero : extract B (boundary c) = 0 := by
    rw [← hboundary]
    apply extract_projection_eq_zero_of_not_subset G B hbad ∅
    intro hsub
    have he : B.toFinset = ∅ := Finset.subset_empty.mp hsub
    exact hBne (by simpa using he)
  rw [extract_boundary,extract_eq_extract_projection G B hB hbad c hmax] at hzero
  exact (smul_eq_zero.mp hzero).resolve_left (pow_ne_zero _ (by norm_num))

end TernaryPoly.MaximalBadFaceCycle
