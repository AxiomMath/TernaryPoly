module

public import TernaryPeriodPolynomials.Building.RankTwo.GoodComplex

@[expose] public section


/-!
# Appendix A, rank two: bad vertices are never adjacent and the link of a bad vertex is a bi-infinite path of good vertices

Formalized by Claude Sonnet 5.5.

> Two bad vertices cannot be adjacent, since their reductions lie in the same one-dimensional subspace.  The link of a bad vertex is therefore a bi-infinite path of good vertices.

Library objects (rank two): `RankTwoAugmentedFrames.ambient` is the augmented-frame complex of `ℤ²` (faces: nonempty subsets of `{g e₀, g e₁, g(e₀+e₁)}`, `g ∈ GL₂(ℤ)`), `RankTwoGoodComplex.Good φ L`
is "the primitive generator of `L` has nonzero image under the nonzero functional `φ` on `(ℤ/3)²`" (the descended covector `ℓ`), `RankTwoVertexLinks.vertexLink g` is the full link of the vertex `g e₀`
(faces: nonempty `s` with `{g e₀} ∪ s` ambient, `g e₀ ∉ s`).  For a basis `g = (b, u₀)` the lifts `u_k = u₀ + k b` are `RankTwoVertexLinks.coordinateLine g k`.

* `bad_vertices_not_adjacent`: for every nonzero functional `φ` two distinct bad lines never span an ambient edge.
* `bad_vertex_link_is_path`: for a bad line `L` there is a basis `g` with `g e₀ = L` such that the link of `L` is entirely good (`vertexLink g ≤ good φ`, so the good link is the full link), has no face with
  more than two vertices, its vertices are exactly the lifts `u_k` (`k ∈ ℤ`, each once), and two lifts are adjacent iff `|k - l| = 1`: the link graph is isomorphic to the bi-infinite path `pathGraphZ`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.AppendixA.Links

open TernaryPoly TernaryPoly.RankTwoAugmentedFrames TernaryPoly.RankTwoVertexLinks
  TernaryPoly.RankTwoGoodComplex TernaryPoly.GoodLinkExtraction

local instance : DecidableEq RationalLine2 := Classical.decEq _

/-- The bi-infinite path: `k ~ l` iff `|k - l| = 1`. -/
def pathGraphZ : SimpleGraph ℤ where
  Adj k l := (k - l).natAbs = 1
  symm := ⟨fun k l h => by
    show (l - k).natAbs = 1
    rw [show l - k = -(k - l) by ring, Int.natAbs_neg]
    exact h⟩
  loopless := ⟨fun k h => by simp at h⟩

/-- The graph on the vertices of the link of `g e₀`: distinct vertices are adjacent iff they span a link edge. -/
def vertexLinkGraph (g : IntegralGL) : SimpleGraph {L : RationalLine2 // {L} ∈ vertexLink g} where
  Adj L M := L ≠ M ∧ {L.val, M.val} ∈ vertexLink g
  symm := ⟨fun L M h => ⟨h.1.symm, by rw [Finset.pair_comm]; exact h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- The lifts `u_k = u₀ + k b` of the basis `g = (b, u₀)` index the vertices of the link of `b` bijectively. -/
def lifts (g : IntegralGL) : ℤ ≃ {L : RationalLine2 // {L} ∈ vertexLink g} :=
  Equiv.ofBijective (fun k => ⟨coordinateLine g k, coordinate_mem_link g k⟩)
    ⟨fun k l h => coordinateLine_injective g (congrArg Subtype.val h),
     fun L => by
       obtain ⟨k, hk⟩ := exists_coordinate g L.val L.property
       exact ⟨k, Subtype.ext hk⟩⟩

/-- **The link of the vertex `b = g e₀` is the bi-infinite path of the lifts `u_k`.** -/
def linkPathIso (g : IntegralGL) : pathGraphZ ≃g vertexLinkGraph g where
  toEquiv := lifts g
  map_rel_iff' := by
    intro k l
    show (lifts g k ≠ lifts g l ∧ {(lifts g k).val, (lifts g l).val} ∈ vertexLink g) ↔
      (k - l).natAbs = 1
    change (lifts g k ≠ lifts g l ∧
      {coordinateLine g k, coordinateLine g l} ∈ vertexLink g) ↔ (k - l).natAbs = 1
    by_cases hkl : k = l
    · subst hkl; simp
    · have hne : lifts g k ≠ lifts g l := fun h => hkl ((lifts g).injective h)
      rw [pair_mem_link_iff_natAbs g k l hkl]
      exact ⟨fun h => h.2, fun h => ⟨hne, h⟩⟩

/-- The lift `u_k` is the line spanned by `k b + u₀`, where `b = g e₀` and `u₀ = g e₁`. -/
theorem lift_span (g : IntegralGL) (k : ℤ) :
    (coordinateLine g k).val =
      Submodule.span ℚ {(k : ℚ) • rationalRepresentation g (template 0) +
        rationalRepresentation g (template 1)} := by
  have h : rationalVector (coordinateVector k) = (k : ℚ) • template 0 + template 1 := by
    funext i
    fin_cases i <;> simp [rationalVector, coordinateVector, template]
  change Submodule.span ℚ {rationalRepresentation g (rationalVector (coordinateVector k))} = _
  rw [h, map_add, map_smul]

/-- **Two distinct bad vertices are never adjacent** (rank two, any nonzero covector `φ`). -/
theorem bad_vertices_not_adjacent (φ : Functional) (hφ : φ ≠ 0) (L M : RationalLine2) (hne : L ≠ M)
    (hL : ¬ Good φ L) (hM : ¬ Good φ M) : {L, M} ∉ ambient :=
  fun hf => (edge_good_or_good φ hφ L M hne hf).elim hL hM

/-- **The link of a bad vertex is a bi-infinite path of good vertices.**  For a bad line `L` there is
a basis `g` with `g e₀ = L` such that
* every face of the link of `L` consists of good vertices (so the good link equals the full link), and has at most two vertices;
* the vertices of the link are exactly the lifts `u_k` (each once), all good;
* `u_k, u_l` span an edge iff `|k - l| = 1`: the link graph is the bi-infinite path. -/
theorem bad_vertex_link_is_path (φ : Functional) (hφ : φ ≠ 0) (L : RationalLine2) (hL : ¬ Good φ L) :
    ∃ g : IntegralGL, augmentedLine g 0 = L ∧ vertexLink g ≤ good φ ∧
      (∀ s ∈ vertexLink g, s.card ≤ 2) ∧
      (∀ k : ℤ, Good φ (coordinateLine g k)) ∧
      (∀ M : RationalLine2, {M} ∈ vertexLink g ↔ ∃! k : ℤ, coordinateLine g k = M) ∧
      (∀ k l : ℤ, k ≠ l → ({coordinateLine g k, coordinateLine g l} ∈ vertexLink g ↔ (k - l).natAbs = 1)) ∧
      Nonempty (pathGraphZ ≃g vertexLinkGraph g) := by
  obtain ⟨g, hg⟩ := rationalLine_eq_augmentedLine L
  have hgb : ¬ Good φ (augmentedLine g 0) := by rw [hg]; exact hL
  have hle := bad_vertexLink_le_good φ hφ g hgb
  refine ⟨g, hg, hle, fun s hs => link_card_le_two g hs, ?_, ?_, ?_, ⟨linkPathIso g⟩⟩
  · intro k
    have hs := hle (coordinate_mem_link g k)
    exact hs.2 _ (Finset.mem_singleton_self _)
  · intro M
    constructor
    · intro h; exact existsUnique_coordinate g M h
    · rintro ⟨k, hk, -⟩
      rw [← hk]
      exact coordinate_mem_link g k
  · intro k l hkl
    exact pair_mem_link_iff_natAbs g k l hkl

end TernaryPeriodPolynomials.Argument.AppendixA.Links
