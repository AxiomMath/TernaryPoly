module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Data.Rat.Lemmas
public import Lean.Elab.Tactic.Omega
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.GroupWithZero.Indicator
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.Data.Fintype.Order
public import Mathlib.Data.List.Enum
public import Mathlib.Data.String.Defs
public import Mathlib.Lean.Elab.InfoTree
public import Mathlib.Lean.Elab.Tactic.Basic
public import Mathlib.Lean.Elab.Tactic.Meta
public import Mathlib.Lean.Expr.ExtraRecognizers
public import Mathlib.Lean.Expr.Rat
public import Mathlib.Lean.GoalsLocation
public import Mathlib.Lean.MessageData.Trace
public import Mathlib.Lean.Meta
public import Mathlib.Lean.Meta.Basic
public import Mathlib.Lean.Meta.KAbstractPositions
public import Mathlib.Lean.Meta.Tactic.Rewrite
public import Mathlib.Lean.PrettyPrinter.Delaborator
public import Mathlib.RingTheory.Finiteness.Lattice
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Tactic.Basify.Attr

@[expose] public section

noncomputable section
namespace TernaryPoly.GoodIncidenceConnected

abbrev Space := Fin 3 → ℚ
abbrev RationalSubspace := Submodule ℚ Space

/-- A good line is a one-dimensional rational subspace satisfying `Good`. -/
abbrev Line (Good : RationalSubspace → Prop) :=
  {L : RationalSubspace // Module.finrank ℚ L = 1 ∧ Good L}

/-- A good plane is a two-dimensional rational subspace containing a good line. -/
abbrev Plane (Good : RationalSubspace → Prop) :=
  {P : RationalSubspace // Module.finrank ℚ P = 2 ∧ ∃ L : Line Good, L.val ≤ P}

/-- The two types of vertices are kept separate by the disjoint sum. -/
abbrev Vertex (Good : RationalSubspace → Prop) := Line Good ⊕ Plane Good

/-- The bipartite incidence relation is strict containment of a line in a plane. -/
def Adj (Good : RationalSubspace → Prop) : Vertex Good → Vertex Good → Prop
  | .inl L, .inr P => L.val < P.val
  | .inr P, .inl L => L.val < P.val
  | _, _ => False

/-- The actual simple incidence graph of good rational lines and planes. -/
def graph (Good : RationalSubspace → Prop) : SimpleGraph (Vertex Good) where
  Adj := Adj Good
  symm.symm u v h := by cases u <;> cases v <;> exact h
  loopless.irrefl v h := by cases v <;> exact h

/-- Distinct rational lines span a rational plane. -/
theorem finrank_sup_of_distinct_lines (L M : RationalSubspace)
    (hL : Module.finrank ℚ L = 1) (hM : Module.finrank ℚ M = 1) (hne : L ≠ M) :
    Module.finrank ℚ (L ⊔ M : RationalSubspace) = 2 := by
  have hlt : L < L ⊔ M := by
    apply lt_of_le_of_ne le_sup_left
    intro heq
    apply hne
    have hML : M ≤ L := by rw [heq]; exact le_sup_right
    exact (Submodule.eq_of_le_of_finrank_eq hML (hM.trans hL.symm)).symm
  have hlo := Submodule.finrank_lt_finrank_of_lt hlt
  have hhi := Submodule.finrank_add_le_finrank_add_finrank L M
  omega

variable (Good : RationalSubspace → Prop)

/-- For a line and a plane, containment is automatically strict. -/
theorem line_lt_plane {L : Line Good} {P : Plane Good} (h : L.val ≤ P.val) :
    L.val < P.val := by
  apply lt_of_le_of_ne h
  intro heq
  have hr := congrArg (fun S : RationalSubspace => Module.finrank ℚ S) heq
  have hL := L.property.1
  have hP := P.property.1
  omega

/-- The joining plane is good because it contains the first good line. -/
def spanPlane (L M : Line Good) (hne : L ≠ M) : Plane Good :=
  ⟨L.val ⊔ M.val,
    finrank_sup_of_distinct_lines L.val M.val L.property.1 M.property.1
      (fun h => hne (Subtype.ext h)),
    ⟨L, le_sup_left⟩⟩

/-- The explicit zero-edge or two-edge walk between good lines. -/
def lineWalk (L M : Line Good) : (graph Good).Walk (.inl L) (.inl M) := by
  classical
  by_cases h : L = M
  · subst M
    exact .nil
  · let P := spanPlane Good L M h
    have hLP : (graph Good).Adj (.inl L) (.inr P) :=
      line_lt_plane Good le_sup_left
    have hPM : (graph Good).Adj (.inr P) (.inl M) :=
      line_lt_plane Good le_sup_right
    exact .cons hLP (.cons hPM .nil)

theorem lineWalk_length_le_two (L M : Line Good) : (lineWalk Good L M).length ≤ 2 := by
  classical
  by_cases h : L = M
  · subst M
    simp only [lineWalk]
    exact Nat.zero_le 2
  · simp only [lineWalk, dite_eq_right h]
    exact le_rfl

/-- Each vertex comes with a good line that it contains. -/
def anchor : Vertex Good → Line Good
  | .inl L => L
  | .inr P => P.property.2.choose

/-- The chosen good line is joined to its vertex by at most one incidence edge. -/
def anchorWalk : (v : Vertex Good) → (graph Good).Walk (.inl (anchor Good v)) v
  | .inl _ => .nil
  | .inr P => .cons
      (show (graph Good).Adj (.inl (anchor Good (.inr P))) (.inr P) from
        line_lt_plane Good P.property.2.choose_spec) .nil

theorem anchorWalk_length_le_one (v : Vertex Good) : (anchorWalk Good v).length ≤ 1 := by
  cases v with
  | inl L => exact Nat.zero_le 1
  | inr P => exact le_rfl

/-- A concrete incidence walk between arbitrary vertices, using their good-line anchors. -/
def vertexWalk (u v : Vertex Good) : (graph Good).Walk u v :=
  (anchorWalk Good u).reverse.append
    ((lineWalk Good (anchor Good u) (anchor Good v)).append (anchorWalk Good v))

theorem vertexWalk_length_le_four (u v : Vertex Good) : (vertexWalk Good u v).length ≤ 4 := by
  have hu := anchorWalk_length_le_one Good u
  have hv := anchorWalk_length_le_one Good v
  have hl := lineWalk_length_le_two Good (anchor Good u) (anchor Good v)
  simp only [vertexWalk, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse]
  omega

/-- Removing repetitions gives genuine simple paths with the same endpoints. -/
def vertexPath (u v : Vertex Good) : (graph Good).Path u v := by
  classical
  exact (vertexWalk Good u v).toPath

theorem vertexPath_length_le_four (u v : Vertex Good) : (vertexPath Good u v).val.length ≤ 4 := by
  classical
  exact (vertexWalk Good u v).length_bypass_le_length.trans (vertexWalk_length_le_four Good u v)

/-- All vertices are reachable, even before a nonempty good-line hypothesis is chosen. -/
theorem preconnected : (graph Good).Preconnected :=
  fun u v => (vertexWalk Good u v).reachable

/-- One good rational line suffices for connectedness of the whole good incidence graph. -/
theorem connected (hgood : ∃ L : RationalSubspace, Module.finrank ℚ L = 1 ∧ Good L) :
    (graph Good).Connected := by
  obtain ⟨L, hL⟩ := hgood
  exact { preconnected := preconnected Good, nonempty := ⟨.inl ⟨L, hL⟩⟩ }

end TernaryPoly.GoodIncidenceConnected
