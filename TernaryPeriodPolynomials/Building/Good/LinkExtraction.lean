module

public import TernaryPeriodPolynomials.Building.BadFace.Contraction
public import TernaryPeriodPolynomials.Building.AugmentedFrame.FrameComplex

@[expose] public section


noncomputable section
namespace TernaryPoly.GoodLinkExtraction
open OrientedListChains OrientedChainContraction OrientedVertexExtraction
open OrientedChainProjection BadFaceContraction
variable {V : Type*}
local instance : DecidableEq V := Classical.decEq V

/-- The actual star of a finite face: adjoining the fixed vertices remains an ambient face. -/
def star (C : PreAbstractSimplicialComplex V) (B : Finset V) :
    PreAbstractSimplicialComplex V where
  faces := {s | s.Nonempty ∧ B ∪ s ∈ C}
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨hs.1,?_⟩
    intro t hts ht
    refine ⟨ht,?_⟩
    exact (C.isRelLowerSet_faces hs.2).2
      (Finset.union_subset_union (Finset.Subset.refl B) hts)
      (ht.mono Finset.subset_union_right)

/-- The actual Good link on the ambient vertex type, with all-Good residual faces. -/
def goodLink (C : PreAbstractSimplicialComplex V) (G : V → Prop) (B : Finset V) :
    PreAbstractSimplicialComplex V where
  faces := {s | s ∈ star C B ∧ ∀ a ∈ s, G a}
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨((star C B).isRelLowerSet_faces hs.1).1,?_⟩
    intro t hts ht
    exact ⟨((star C B).isRelLowerSet_faces hs.1).2 hts ht,
      fun a ha => hs.2 a (hts ha)⟩

@[simp] theorem mem_star (C : PreAbstractSimplicialComplex V) (B s : Finset V) :
    s ∈ star C B ↔ s.Nonempty ∧ B ∪ s ∈ C := Iff.rfl

@[simp] theorem mem_goodLink (C : PreAbstractSimplicialComplex V) (G : V → Prop)
    (B s : Finset V) :
    s ∈ goodLink C G B ↔ s.Nonempty ∧ B ∪ s ∈ C ∧ ∀ a ∈ s, G a := by
  change ((s.Nonempty ∧ B ∪ s ∈ C) ∧ ∀ a ∈ s, G a) ↔ _
  exact and_assoc

/-- Good residual faces are disjoint from an all-bad fixed face. -/
theorem goodLink_disjoint (C : PreAbstractSimplicialComplex V) (G : V → Prop)
    (B : Finset V) (hB : ∀ a ∈ B, ¬G a) {s : Finset V}
    (hs : s ∈ goodLink C G B) : Disjoint B s := by
  apply Finset.disjoint_left.mpr
  intro a ha hsa
  exact hB a ha (hs.2 a hsa)

/-- Every simplex surviving the exact B projection literally contains every vertex of B. -/
theorem subset_of_badVertices_eq (G : V → Prop) (B : Finset V) (l : List V)
    (hB : badVertices G l = B) : B ⊆ l.toFinset := by
  intro a ha
  have h := (mem_badVertices G l a).mp (hB.symm ▸ ha)
  exact List.mem_toFinset.mpr h.1

/-- A surviving ambient simplex is star-supported; the empty augmented simplex is handled separately. -/
theorem allowed_star_of_badVertices_eq (C : PreAbstractSimplicialComplex V)
    (G : V → Prop) (B : Finset V) (l : List V)
    (hl : Allowed C l) (hB : badVertices G l = B) : Allowed (star C B) l := by
  rcases hl with rfl | hl
  · exact Or.inl rfl
  · apply Or.inr
    refine ⟨(C.isRelLowerSet_faces hl).1,?_⟩
    rw [Finset.union_eq_right.mpr (subset_of_badVertices_eq G B l hB)]
    exact hl

/-- Exact bad-face projection sends actual ambient chains to the corresponding actual star. -/
theorem badFaceProjection_mem_star (C : PreAbstractSimplicialComplex V)
    (G : V → Prop) (B : Finset V) (n : ℕ) {c : Chain V} (hc : c ∈ chains C n) :
    badFaceProjection G B c ∈ chains (star C B) n := by
  classical
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨l,hlen,hl,rfl⟩ := hc
    by_cases hB : badVertices G l = B
    · rw [badFaceProjection_simplex,ite_eq_left hB]
      simpa only [hlen] using simplex_mem_chains (star C B) l
        (allowed_star_of_badVertices_eq C G B l hl hB)
    · rw [badFaceProjection_simplex,ite_eq_right hB]
      exact (chains (star C B) n).zero_mem
  | zero => simpa only [map_zero] using (chains (star C B) n).zero_mem
  | add c d hc hd ihc ihd =>
    simpa only [map_add] using (chains (star C B) n).add_mem ihc ihd
  | smul q c hc ih =>
    simpa only [map_smul] using (chains (star C B) n).smul_mem q ih

/-- Successive actual vertex contractions preserve any precomplex and lower vertex degree by list length. -/
theorem extract_mem_chains (C : PreAbstractSimplicialComplex V) (B : List V) (n : ℕ)
    {c : Chain V} (hc : c ∈ chains C (n+B.length)) : extract B c ∈ chains C n := by
  induction B generalizing c with
  | nil => simpa only [extract,List.length_nil,Nat.add_zero,LinearMap.id_apply] using hc
  | cons a B ih =>
    change extract B (atVertex a c) ∈ chains C n
    apply ih
    exact contraction_mem_chains (vertexWeight a) C (n+B.length)
      (by simpa only [List.length_cons,Nat.add_assoc] using hc)

/-- An exact empty bad face means that all vertices of the simplex are Good. -/
theorem all_good_of_badVertices_eq_empty (G : V → Prop) (l : List V)
    (hl : badVertices G l = ∅) : ∀ a ∈ l, G a := by
  classical
  intro a ha
  by_contra hbad
  have h := (mem_badVertices G l a).mpr ⟨ha,hbad⟩
  rw [hl] at h
  simp at h

/-- Empty bad-face projection sends star chains to actual Good-link chains. -/
theorem empty_projection_mem_goodLink (C : PreAbstractSimplicialComplex V)
    (G : V → Prop) (B : Finset V) (n : ℕ) {c : Chain V}
    (hc : c ∈ chains (star C B) n) :
    badFaceProjection G ∅ c ∈ chains (goodLink C G B) n := by
  classical
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨l,hlen,hl,rfl⟩ := hc
    by_cases hgood : badVertices G l = ∅
    · rw [badFaceProjection_simplex,ite_eq_left hgood]
      have ha : Allowed (goodLink C G B) l := by
        rcases hl with rfl | hl
        · exact Or.inl rfl
        · exact Or.inr ⟨hl,fun a ha => all_good_of_badVertices_eq_empty G l hgood a
            (List.mem_toFinset.mp ha)⟩
      simpa only [hlen] using simplex_mem_chains (goodLink C G B) l ha
    · rw [badFaceProjection_simplex,ite_eq_right hgood]
      exact (chains (goodLink C G B) n).zero_mem
  | zero => simpa only [map_zero] using (chains (goodLink C G B) n).zero_mem
  | add c d hc hd ihc ihd =>
    simpa only [map_add] using (chains (goodLink C G B) n).add_mem ihc ihd
  | smul q c hc ih =>
    simpa only [map_smul] using (chains (goodLink C G B) n).smul_mem q ih

/-- Star support and the exact all-Good support identity together give actual link-chain membership. -/
theorem mem_goodLink_of_exact_good_support (C : PreAbstractSimplicialComplex V)
    (G : V → Prop) (B : Finset V) (n : ℕ) {c : Chain V}
    (hc : c ∈ chains (star C B) n) (hgood : badFaceProjection G ∅ c = c) :
    c ∈ chains (goodLink C G B) n := by
  rw [← hgood]
  exact empty_projection_mem_goodLink C G B n hc

/-- The extracted coefficient of an exact all-bad face belongs to its genuine Good-link chains. -/
theorem extract_badFaceProjection_mem_goodLink (C : PreAbstractSimplicialComplex V)
    (G : V → Prop) (B : List V) (hB : B.Nodup) (hbad : ∀ a ∈ B, ¬G a)
    (n : ℕ) {c : Chain V} (hc : c ∈ chains C (n+B.length)) :
    extract B (badFaceProjection G B.toFinset c) ∈ chains (goodLink C G B.toFinset) n := by
  apply mem_goodLink_of_exact_good_support C G B.toFinset n
  · exact extract_mem_chains (star C B.toFinset) B n
      (badFaceProjection_mem_star C G B.toFinset (n+B.length) hc)
  · exact extract_projection_has_good_support G B hB hbad c

open ModThreeGoodAction AugmentedFrameComplex
local instance : DecidableEq RationalLine := Classical.decEq _

/-- The actual auxiliary star inside the integral augmented-frame complex. -/
def ambientStar (B : Finset RationalLine) : PreAbstractSimplicialComplex RationalLine :=
  star ambient B

/-- The genuine Good link of an actual finite bad face in the augmented-frame complex. -/
def augmentedGoodLink (B : Finset RationalLine) : PreAbstractSimplicialComplex RationalLine :=
  goodLink ambient (fun L => Good L.val) B

/-- Actual ambient specialization: exact bad-face coefficients have correctly graded Good-link support. -/
theorem ambient_extract_mem_goodLink (B : List RationalLine) (hB : B.Nodup)
    (hbad : ∀ L ∈ B, ¬Good L.val) (n : ℕ) {c : Chain RationalLine}
    (hc : c ∈ chains ambient (n+B.length)) :
    extract B (badFaceProjection (fun L => Good L.val) B.toFinset c) ∈
      chains (augmentedGoodLink B.toFinset) n := by
  simpa only [augmentedGoodLink] using
    extract_badFaceProjection_mem_goodLink ambient (fun L => Good L.val) B hB hbad n hc

end TernaryPoly.GoodLinkExtraction
