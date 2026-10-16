module

public import TernaryPeriodPolynomials.Building.RankTwo.HeightLinks
public import Mathlib.Data.ZMod.Basic

@[expose] public section

noncomputable section
namespace TernaryPoly.RankTwoGoodComplex
open RankTwoAugmentedFrames RankTwoVertexLinks RankTwoHeightLinks
open OrientedListChains GoodLinkExtraction
local instance : DecidableEq RationalLine2 := Classical.decEq _

abbrev ResidueSpace := Fin 2 → ZMod 3
abbrev Functional := ResidueSpace →ₗ[ZMod 3] ZMod 3

/-- Literal coordinatewise reduction of the integral rank-two lattice. -/
def reduction (v : IntegralVector) : ResidueSpace := fun i => (v i : ZMod 3)

theorem reduction_neg (v : IntegralVector) : reduction (-v) = -reduction v := by
  funext i
  simp [reduction]

/-- A primitive rational line is retained when the nonzero residue functional detects it. -/
def Good (φ : Functional) (L : RationalLine2) : Prop :=
  φ (reduction (primitiveGenerator L)) ≠ 0

/-- The residue nonvanishing predicate is independent of the chosen primitive generator. -/
theorem good_iff_primitive (φ : Functional) (L : RationalLine2)
    {v : IntegralVector} (hv : Primitive v)
    (hs : Submodule.span ℚ {rationalVector v} = L.val) :
    Good φ L ↔ φ (reduction v) ≠ 0 := by
  rcases primitive_eq_or_neg_of_span_eq (primitiveGenerator_primitive L) hv
    ((primitiveGenerator_span L).trans hs.symm) with he | he
  · simp only [Good,he]
  · simp only [Good,he,reduction_neg,map_neg,neg_ne_zero]

/-- The actual full Good subcomplex of literal rank-two augmented frames. -/
def good (φ : Functional) : PreAbstractSimplicialComplex RationalLine2 where
  faces := {s | s ∈ ambient ∧ ∀ L ∈ s, Good φ L}
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨(ambient.isRelLowerSet_faces hs.1).1,?_⟩
    intro t hts ht
    exact ⟨(ambient.isRelLowerSet_faces hs.1).2 hts ht,fun L hL => hs.2 L (hts hL)⟩

theorem good_le_ambient (φ : Functional) : good φ ≤ ambient := fun _ h => h.1

theorem allowed_good_iff (φ : Functional) (l : List RationalLine2) :
    Allowed (good φ) l ↔ Allowed ambient l ∧ ∀ L ∈ l, Good φ L := by
  classical
  constructor
  · rintro (rfl | hl)
    · exact ⟨Or.inl rfl,by simp⟩
    · exact ⟨Or.inr hl.1,fun L hL => hl.2 L (List.mem_toFinset.mpr hL)⟩
  · rintro ⟨hl,hg⟩
    rcases hl with rfl | hl
    · exact Or.inl rfl
    · exact Or.inr ⟨hl,fun L hL => hg L (List.mem_toFinset.mp hL)⟩

theorem good_column_iff (φ : Functional) (g : IntegralGL) (j : Fin 2) :
    Good φ (augmentedLine g j.castSucc) ↔ φ (reduction (g.val.col j)) ≠ 0 := by
  apply good_iff_primitive φ _ (column_primitive g j)
  change _ = Submodule.span ℚ {rationalRepresentation g (template j.castSucc)}
  rw [representation_column]
  rfl

/-- A functional vanishing on both columns of an actual integral basis is zero modulo three. -/
theorem functional_eq_zero_of_columns (φ : Functional) (g : IntegralGL)
    (h0 : φ (reduction (g.val.col 0)) = 0) (h1 : φ (reduction (g.val.col 1)) = 0) : φ = 0 := by
  let M := Matrix.GeneralLinearGroup.map (Int.castRingHom (ZMod 3)) g
  have hc (v : ResidueSpace) : M.val.mulVec v =
      v 0 • reduction (g.val.col 0) + v 1 • reduction (g.val.col 1) := by
    funext i
    simp [M,reduction,Matrix.mulVec,dotProduct,Fin.sum_univ_two,
      Matrix.GeneralLinearGroup.map_apply,Matrix.col,mul_comm]
  have hi (v : ResidueSpace) : M.val.mulVec (M⁻¹.val.mulVec v) = v := by
    rw [Matrix.mulVec_mulVec,← Units.val_mul,mul_inv_cancel,Units.val_one,Matrix.one_mulVec]
  apply LinearMap.ext
  intro v
  change φ v = 0
  rw [← hi v,hc,map_add,map_smul,map_smul,h0,h1,smul_zero,smul_zero,add_zero]

/-- Two distinct bad vertices cannot form an actual ambient edge. -/
theorem edge_good_or_good (φ : Functional) (hφ : φ ≠ 0) (L M : RationalLine2)
    (hne : L ≠ M) (hf : {L,M} ∈ ambient) : Good φ L ∨ Good φ M := by
  obtain ⟨g,h0,h1⟩ := edge_basis L M hne (by
    convert hf using 1
    ext A
    simp only [Finset.mem_insert,Finset.mem_singleton])
  by_contra h
  push Not at h
  apply hφ
  apply functional_eq_zero_of_columns φ g
  · have hg : ¬Good φ (augmentedLine g 0) := by rw [h0]; exact h.1
    exact not_not.mp ((not_congr (good_column_iff φ g 0)).mp hg)
  · have hg : ¬Good φ (augmentedLine g 1) := by rw [h1]; exact h.2
    exact not_not.mp ((not_congr (good_column_iff φ g 1)).mp hg)

/-- Every actual neighbor of a bad vertex is Good. -/
theorem neighbor_good (φ : Functional) (hφ : φ ≠ 0) (L M : RationalLine2)
    (hL : ¬Good φ L) (hne : M ≠ L) (hf : {L,M} ∈ ambient) : Good φ M :=
  (edge_good_or_good φ hφ L M (Ne.symm hne) hf).resolve_left hL

/-- Every vertex in the full actual link of a bad vertex is retained. -/
theorem bad_vertexLink_le_good (φ : Functional) (hφ : φ ≠ 0) (g : IntegralGL)
    (hg : ¬Good φ (augmentedLine g 0)) : vertexLink g ≤ good φ := by
  intro s hs
  refine ⟨link_face_ambient g hs,?_⟩
  intro L hL
  have hsingle := ((vertexLink g).isRelLowerSet_faces hs).2
    (Finset.singleton_subset_iff.mpr hL) (by simp)
  obtain ⟨hne,hface⟩ := (singleton_mem_link_iff g L).mp hsingle
  exact neighbor_good φ hφ _ L hg hne hface

/-- A bad vertex always has an actual Good neighbor. -/
theorem exists_good_neighbor (φ : Functional) (hφ : φ ≠ 0) (L : RationalLine2)
    (hL : ¬Good φ L) : ∃ M : RationalLine2, M ≠ L ∧ {L,M} ∈ ambient ∧ Good φ M := by
  obtain ⟨g,hg⟩ := rationalLine_eq_augmentedLine L
  have hm := coordinate_mem_link g 0
  obtain ⟨hne,hface⟩ := (singleton_mem_link_iff g _).mp hm
  rw [hg] at hne hface
  exact ⟨coordinateLine g 0,hne,hface,neighbor_good φ hφ L _ hL hne hface⟩

/-- Every full Good subcomplex inherits actual top-boundary injectivity. -/
theorem top_boundary_injective (φ : Functional) {c d : Chain RationalLine2}
    (hc : c ∈ chains (good φ) 3) (hd : d ∈ chains (good φ) 3)
    (he : boundary c = boundary d) : c = d :=
  subcomplex_top_boundary_injective (good φ) (good_le_ambient φ) hc hd he

theorem top_cycle_eq_zero (φ : Functional) {c : Chain RationalLine2}
    (hc : c ∈ chains (good φ) 3) (hd : boundary c = 0) : c = 0 :=
  subcomplex_top_cycle_eq_zero (good φ) (good_le_ambient φ) hc hd

end TernaryPoly.RankTwoGoodComplex
