module

public import Mathlib.Topology.Bases
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.List.Enum
public import Mathlib.Data.String.Defs
public import Mathlib.Lean.Elab.InfoTree
public import Mathlib.Lean.Elab.Tactic.Basic
public import Mathlib.Lean.Elab.Tactic.Meta
public import Mathlib.Lean.Expr.Basic
public import Mathlib.Lean.Expr.ExtraRecognizers
public import Mathlib.Lean.GoalsLocation
public import Mathlib.Lean.MessageData.Trace
public import Mathlib.Lean.Meta
public import Mathlib.Lean.Meta.Basic
public import Mathlib.Lean.Meta.KAbstractPositions
public import Mathlib.Lean.PrettyPrinter.Delaborator
public import Mathlib.Tactic.Basify.Attr
public import Mathlib.Topology.ContinuousOn
public import Mathlib.Topology.WithTopology

@[expose] public section


namespace TernaryPoly.OpenBasisGluing
open TopologicalSpace

variable {X : Type} {P : Set X → Prop} {B : Set (Set X)}

/-- Finite unions satisfy a gluing property when it holds on an intersection-stable family,
including the empty set, and satisfies the genuine three-term union criterion. -/
theorem finite_union (hB : ∀ b ∈ B, P b) (hEmpty : P ∅)
    (hInter : ∀ b ∈ B, ∀ c ∈ B, b ∩ c ∈ B)
    (hGlue : ∀ b c, P b → P c → P (b ∩ c) → P (b ∪ c))
    (n : ℕ) (f : Fin n → Set X) (hf : ∀ i, f i ∈ B) : P (⋃ i, f i) := by
  induction n with
  | zero => simpa using hEmpty
  | succ n ih =>
    rw [Set.iUnion_fin_add_one_eq_iUnion_succ]
    apply hGlue
    · exact hB _ (hf 0)
    · exact ih (fun i => f i.succ) (fun i => hf i.succ)
    · rw [Set.inter_iUnion]
      exact ih (fun i => f 0 ∩ f i.succ) (fun i => hInter _ (hf 0) _ (hf i.succ))

/-- Countable unions of an intersection-stable family follow from binary gluing and continuity
for increasing unions, without assuming closure under arbitrary unions. -/
theorem countable_union (hB : ∀ b ∈ B, P b) (hEmpty : P ∅)
    (hInter : ∀ b ∈ B, ∀ c ∈ B, b ∩ c ∈ B)
    (hGlue : ∀ b c, P b → P c → P (b ∩ c) → P (b ∪ c))
    (hIncreasing : ∀ s : ℕ → Set X, Monotone s → (∀ n, P (s n)) → P (⋃ n, s n))
    (f : ℕ → Set X) (hf : ∀ n, f n ∈ B) : P (⋃ n, f n) := by
  let s : ℕ → Set X := fun n => ⋃ i : Fin n, f i.val
  have hs : Monotone s := by
    intro n m hnm x hx
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_iUnion.mpr ⟨⟨i.val,lt_of_lt_of_le i.isLt hnm⟩,hi⟩
  have heq : (⋃ n, s n) = ⋃ n, f n := by
    ext x
    constructor
    · intro hx
      obtain ⟨n,hn⟩ := Set.mem_iUnion.mp hx
      obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hn
      exact Set.mem_iUnion.mpr ⟨i.val,hi⟩
    · intro hx
      obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hx
      exact Set.mem_iUnion.mpr ⟨i+1,Set.mem_iUnion.mpr ⟨⟨i,by omega⟩,hi⟩⟩
  rw [← heq]
  exact hIncreasing s hs (fun n => finite_union hB hEmpty hInter hGlue n (fun i => f i.val) (fun i => hf i.val))

variable [TopologicalSpace X] [SecondCountableTopology X]

/-- On a second-countable space, an intersection-stable open basis, genuine binary gluing,
and increasing-union continuity prove the property on every open subset. -/
theorem open_induction (hBasis : IsTopologicalBasis B) (hB : ∀ b ∈ B, P b) (hEmpty : P ∅)
    (hInter : ∀ b ∈ B, ∀ c ∈ B, b ∩ c ∈ B)
    (hGlue : ∀ b c, P b → P c → P (b ∩ c) → P (b ∪ c))
    (hIncreasing : ∀ s : ℕ → Set X, Monotone s → (∀ n, P (s n)) → P (⋃ n, s n))
    (s : Set X) (hs : IsOpen s) : P s := by
  classical
  by_cases hempty : s = ∅
  · simpa [hempty] using hEmpty
  obtain ⟨S,hSB,hSc,hS⟩ := hBasis.exists_countable_biUnion_of_isOpen hs
  have hSne : S.Nonempty := by
    by_contra hn
    have hsz : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
    simp only [hsz,Set.mem_empty_iff_false,Set.iUnion_of_empty] at hS
    exact hempty (by simpa using hS)
  obtain ⟨f,hf⟩ := hSc.exists_eq_range hSne
  have heq : s = ⋃ n, f n := by
    rw [hS,hf]
    simp
  rw [heq]
  exact countable_union hB hEmpty hInter hGlue hIncreasing f (fun n => hSB (hf ▸ Set.mem_range_self n))

/-- A version with gluing and continuity required only for open sets. -/
theorem open_induction_of_open (hBasis : IsTopologicalBasis B)
    (hB : ∀ b ∈ B, P b) (hEmpty : P ∅)
    (hInter : ∀ b ∈ B, ∀ c ∈ B, b ∩ c ∈ B)
    (hGlue : ∀ b c, IsOpen b → IsOpen c → P b → P c → P (b ∩ c) → P (b ∪ c))
    (hIncreasing : ∀ s : ℕ → Set X, (∀ n, IsOpen (s n)) → Monotone s →
      (∀ n, P (s n)) → P (⋃ n, s n)) (s : Set X) (hs : IsOpen s) : P s := by
  exact (open_induction (P := fun s => IsOpen s ∧ P s) hBasis
    (fun b hb => ⟨hBasis.isOpen hb, hB b hb⟩) ⟨isOpen_empty, hEmpty⟩ hInter
    (fun b c hb hc hi => ⟨hb.1.union hc.1, hGlue b c hb.1 hc.1 hb.2 hc.2 hi.2⟩)
    (fun s hm hp => ⟨isOpen_iUnion (fun n => (hp n).1),
      hIncreasing s (fun n => (hp n).1) hm (fun n => (hp n).2)⟩) s hs).2

end TernaryPoly.OpenBasisGluing
