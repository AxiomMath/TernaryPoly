module

public import TernaryPeriodPolynomials.Building.RankTwo.GoodComplex
public import TernaryPeriodPolynomials.Building.RankTwo.HeightOne
public import TernaryPeriodPolynomials.Building.OrientedChain.BadFaceDecomposition

@[expose] public section

noncomputable section
namespace TernaryPoly.RankTwoGoodOne
open RankTwoAugmentedFrames RankTwoVertexLinks RankTwoGoodComplex
open OrientedListChains OrientedChainJoin OrientedChainProjection OrientedVertexExtraction
open OrientedBadFaceDecomposition BadFaceContraction PositiveChainSeparation
local instance : DecidableEq RationalLine2 := Classical.decEq _

/-- Contracting a Good-supported chain at a bad vertex gives zero. -/
theorem bad_contraction_zero (φ : Functional) (L : RationalLine2) (hL : ¬Good φ L)
    (n : ℕ) {c : Chain RationalLine2} (hc : c ∈ chains (good φ) n) : atVertex L c = 0 := by
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨l,_,hl,rfl⟩ := hc
    apply atVertex_simplex_of_not_mem
    intro hm
    exact hL (((allowed_good_iff φ l).mp hl).2 L hm)
  | zero => exact map_zero _
  | add c d hc hd ihc ihd => rw [map_add,ihc,ihd,add_zero]
  | smul q c hc ih => rw [map_smul,ih,smul_zero]

/-- Projection to an empty bad face has actual Good support. -/
theorem empty_projection_mem_good (φ : Functional) (n : ℕ)
    {c : Chain RationalLine2} (hc : c ∈ chains ambient n) :
    badFaceProjection (Good φ) ∅ c ∈ chains (good φ) n := by
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨l,hlen,hl,rfl⟩ := hc
    by_cases he : badVertices (Good φ) l = ∅
    · rw [badFaceProjection_simplex,ite_eq_left he]
      have hh := (allowed_good_iff φ l).mpr
        ⟨hl,GoodLinkExtraction.all_good_of_badVertices_eq_empty (Good φ) l he⟩
      simpa only [hlen] using simplex_mem_chains (good φ) l hh
    · rw [badFaceProjection_simplex,ite_eq_right he]
      exact (chains (good φ) n).zero_mem
  | zero => simpa only [map_zero] using (chains (good φ) n).zero_mem
  | add c d hc hd ihc ihd => simpa only [map_add] using (chains (good φ) n).add_mem ihc ihd
  | smul q c hc ih => simpa only [map_smul] using (chains (good φ) n).smul_mem q ih

/-- A bad-face index containing a Good vertex has identically zero projection. -/
theorem projection_zero_of_good_member (φ : Functional) (s : Finset RationalLine2)
    (L : RationalLine2) (hL : L ∈ s) (hg : Good φ L) (c : Chain RationalLine2) :
    badFaceProjection (Good φ) s c = 0 := by
  have he : badFaceProjection (Good φ) s = (0 : Chain RationalLine2 →ₗ[ℚ] Chain RationalLine2) := by
    apply chain_ext
    intro l
    have hh : badVertices (Good φ) l ≠ s := by
      intro hs
      exact ((mem_badVertices _ _ _).mp (hs.symm ▸ hL)).2 hg
    simp only [badFaceProjection_simplex,ite_eq_right hh,LinearMap.zero_apply]
  rw [he,LinearMap.zero_apply]

/-- Coordinate contractions detect every nonempty bad component on actual finite chains. -/
theorem good_of_bad_contractions_zero (φ : Functional) (n : ℕ)
    {c : Chain RationalLine2} (hc : c ∈ chains ambient n)
    (hz : ∀ L : RationalLine2, ¬Good φ L → atVertex L c = 0) : c ∈ chains (good φ) n := by
  have hproj (s : Finset RationalLine2) (hs : s ≠ ∅) : badFaceProjection (Good φ) s c = 0 := by
    obtain ⟨L,hL⟩ := Finset.nonempty_iff_ne_empty.mpr hs
    by_cases hg : Good φ L
    · exact projection_zero_of_good_member φ s L hL hg c
    · have he := cons_atVertex_of_cons_eq_zero L (badFaceProjection (Good φ) s c)
        (cons_badFaceProjection_eq_zero (Good φ) s L hL c)
      rw [atVertex_badFaceProjection (Good φ) s L hL hg,hz L hg,map_zero,map_zero] at he
      exact he.symm
  obtain ⟨S,hS,_⟩ := exists_badFace_decomposition (Good φ) c
  have he : badFaceProjection (Good φ) ∅ c = c := by
    conv_lhs => rw [← hS]
    rw [map_sum]
    calc
      _ = ∑ s ∈ S, badFaceProjection (Good φ) s c := by
        apply Finset.sum_congr rfl
        intro s _
        by_cases hs : s = ∅
        · subst s
          exact filter_idempotent _ (fun h => by rw [badVertices_perm (Good φ) h]) c
        · rw [hproj s hs,map_zero]
      _ = c := hS
  rw [← he]
  exact empty_projection_mem_good φ n hc

/-- Any actual triangle chain whose boundary is Good is already Good:
all its bad-vertex contractions are cycles in integer-path links and hence vanish. -/
theorem triangle_good_of_boundary_good (φ : Functional) {b : Chain RationalLine2}
    (hb : b ∈ chains ambient 3) (hd : boundary b ∈ chains (good φ) 2) :
    b ∈ chains (good φ) 3 := by
  apply good_of_bad_contractions_zero φ 3 hb
  intro L hL
  apply all_vertex_links_cycle_eq_zero L (atVertex_mem_link ambient L 2 hb)
  have he := OrientedChainContraction.contraction_boundary (vertexWeight L) b
  change atVertex L (boundary b) = -boundary (atVertex L b) at he
  rw [bad_contraction_zero φ L hL 2 hd] at he
  exact neg_eq_zero.mp he.symm

/-- Every actual finite Good one-cycle bounds a Good triangle chain.
Nonzero functionality is unnecessary for this degree. -/
theorem one_cycle_filling (φ : Functional) {c : Chain RationalLine2}
    (hc : c ∈ chains (good φ) 2) (hd : boundary c = 0) :
    ∃ b : Chain RationalLine2, b ∈ chains (good φ) 3 ∧ boundary b = c := by
  obtain ⟨b,hb,hdb⟩ := RankTwoHeightOne.ambient_one_cycle_filling
    (chains_mono (good_le_ambient φ) 2 hc) hd
  exact ⟨b,triangle_good_of_boundary_good φ hb (by rwa [hdb]),hdb⟩

end TernaryPoly.RankTwoGoodOne
