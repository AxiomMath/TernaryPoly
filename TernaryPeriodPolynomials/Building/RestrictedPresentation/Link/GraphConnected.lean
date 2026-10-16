module

public import TernaryPeriodPolynomials.Building.RestrictedPresentation.Link.Main
public import TernaryPeriodPolynomials.Building.Span.ChainComparison

@[expose] public section


/-!
# Lemma A.1: graph connectedness of `L_b`

Formalized by Claude Sonnet 5.5.
Paper: Lemma A.1,
 ("the link `L_b` is connected").

The chain-level statement `connected_link` (`H̃₀(L_b;ℚ) = 0`) implies that any two vertices of `L_b`
are joined by a path of edges of `L_b`: the indicator of the path component of one vertex is an
alternating evaluation on oriented lists which vanishes on boundaries of edge chains.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.AppendixALink

open TernaryPoly TernaryPoly.ModThreeGoodAction TernaryPoly.AugmentedFrameComplex
  TernaryPoly.OrientedListChains TernaryPoly.GoodLinkExtraction

/-- Two distinct lines are adjacent in `L_b` when they span an edge of `L_b`. -/
def Adjacent (b : RationalLine) (x y : RationalLine) : Prop :=
  x ≠ y ∧ ({x,y} : Finset RationalLine) ∈ badLink b

open scoped Classical in
/-- The indicator of a set of vertices, as an evaluation of oriented lists on one-vertex lists. -/
def indicator (P : RationalLine → Prop) : List RationalLine → ℚ
  | [x] => if P x then 1 else 0
  | _ => 0

theorem indicator_alternating (P : RationalLine → Prop) :
    SpanChainComparison.AlternatingLists (indicator P) := by
  intro p x y s
  cases p with
  | nil => simp [indicator]
  | cons u p =>
    cases p with
    | nil => simp [indicator]
    | cons v p => simp [indicator]

theorem indicator_boundary_edges (b : RationalLine) (P : RationalLine → Prop)
    (hP : ∀ x y, Adjacent b x y → (P x ↔ P y)) {c : Chain RationalLine}
    (hc : c ∈ chains (badLink b) 2) :
    SpanChainComparison.evaluate (indicator P) (indicator_alternating P) (boundary c) = 0 := by
  classical
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨l,hlen,hl,rfl⟩ := hc
    obtain ⟨x,y,rfl⟩ := List.length_eq_two.mp hlen
    by_cases hxy : x = y
    · subst hxy
      rw [simplex_repeat_adjacent x [],map_zero,map_zero]
    · have hf : ({x,y} : Finset RationalLine) ∈ badLink b := by
        have := hl.resolve_left (by simp)
        convert this using 1
        ext z; simp
      have hadj : Adjacent b x y := ⟨hxy,hf⟩
      simp only [boundary_cons,boundary_nil,map_zero,sub_zero,cons_simplex,map_sub,
        SpanChainComparison.evaluate_simplex,indicator]
      have := hP x y hadj
      by_cases hx : P x
      · simp [hx,this.mp hx]
      · simp [hx,mt this.mpr hx]
  | zero => simp
  | add x y _ _ hx hy => simp [hx,hy]
  | smul q x _ hx => simp [hx]

/-- **Lemma A.1, graph connectedness**: any two vertices of `L_b` are joined by a path of edges. -/
theorem graph_connected (b : RationalLine) (hb : ¬Good b.val) (a a' : RationalLine)
    (ha : ({a} : Finset RationalLine) ∈ badLink b) (ha' : ({a'} : Finset RationalLine) ∈ badLink b) :
    Relation.ReflTransGen (Adjacent b) a a' := by
  classical
  let P : RationalLine → Prop := fun x => Relation.ReflTransGen (Adjacent b) a x
  have hP : ∀ x y, Adjacent b x y → (P x ↔ P y) := by
    intro x y hxy
    constructor
    · intro h; exact h.tail hxy
    · intro h
      have hyx : Adjacent b y x := ⟨hxy.1.symm,by rw [Finset.pair_comm]; exact hxy.2⟩
      -- from a ~ y, adjacency y ~ x
      exact h.tail hyx
  have hc : simplex [a'] - simplex [a] ∈ chains (badLink b) 1 := by
    apply (chains _ _).sub_mem
    · simpa using simplex_mem_chains (badLink b) [a'] (Or.inr (by simpa using ha'))
    · simpa using simplex_mem_chains (badLink b) [a] (Or.inr (by simpa using ha))
  have hd : boundary (simplex [a'] - simplex [a]) = 0 := by
    simp [boundary_cons]
  obtain ⟨t,ht,hdt⟩ := connected_link b hb hc hd
  have h0 := indicator_boundary_edges b P hP ht
  rw [hdt] at h0
  simp only [map_sub,SpanChainComparison.evaluate_simplex,indicator] at h0
  have hPa : P a := Relation.ReflTransGen.refl
  by_contra hna
  have : ¬ P a' := hna
  simp [this, hPa] at h0

end TernaryPeriodPolynomials.Argument.AppendixALink
