module

public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic.Abel
public import Mathlib.Data.List.Enum
public import Mathlib.Data.String.Defs
public import Mathlib.Lean.Elab.InfoTree
public import Mathlib.Lean.Elab.Tactic.Basic
public import Mathlib.Lean.Elab.Tactic.Meta
public import Mathlib.Lean.Expr.Basic
public import Mathlib.Lean.Expr.ExtraRecognizers
public import Mathlib.Lean.Expr.Rat
public import Mathlib.Lean.GoalsLocation
public import Mathlib.Lean.MessageData.Trace
public import Mathlib.Lean.Meta
public import Mathlib.Lean.Meta.Basic
public import Mathlib.Lean.Meta.KAbstractPositions
public import Mathlib.Lean.PrettyPrinter.Delaborator
public import Mathlib.Tactic.Basify.Attr
public import Mathlib.Util.Qq

@[expose] public section


/-!
# Counting cosets of a saturated set

If `L ≤ L'` are subgroups of an additive commutative group `V` and `S ⊆ V` is stable under
translation by `L'`, then the image of `S` modulo `L` has `[L' : L]` times as many elements as its
image modulo `L'`.

Original work (AxiomDeep, Claude Opus 5.5).
-/

namespace TernaryPeriodPolynomials.HeckeEigen.Satake

variable {V : Type*} [AddCommGroup V]

theorem mem_of_sub_mem {L' : AddSubgroup V} {S : Set V} (hS : ∀ s ∈ S, ∀ l ∈ L', s + l ∈ S)
    {s x : V} (hs : s ∈ S) (hx : x - s ∈ L') : x ∈ S := by
  have := hS s hs (x - s) hx
  simpa using this

/-- The coset images of `S` modulo `L` and modulo `L'`, and the relative index. -/
noncomputable def fiberEquiv (L L' : AddSubgroup V) (h : L ≤ L') (S : Set V)
    (hS : ∀ s ∈ S, ∀ l ∈ L', s + l ∈ S) :
    ((QuotientAddGroup.mk : V → V ⧸ L) '' S) ≃
      ((QuotientAddGroup.mk : V → V ⧸ L') '' S) × (L' ⧸ L.addSubgroupOf L') where
  toFun x :=
    (⟨QuotientAddGroup.mk (Quotient.out x.val), by
        obtain ⟨s, hs, hsx⟩ := x.property
        refine ⟨s, hs, ?_⟩
        apply QuotientAddGroup.eq.mpr
        have h1 : (QuotientAddGroup.mk (Quotient.out x.val) : V ⧸ L) = QuotientAddGroup.mk s := by
          rw [QuotientAddGroup.out_eq', hsx]
        exact h (QuotientAddGroup.eq.mp h1.symm)⟩,
     QuotientAddGroup.mk ⟨Quotient.out x.val -
        Quotient.out (QuotientAddGroup.mk (Quotient.out x.val) : V ⧸ L'), by
        have := QuotientAddGroup.eq.mp
          (QuotientAddGroup.out_eq' (QuotientAddGroup.mk (Quotient.out x.val) : V ⧸ L'))
        simpa [sub_eq_add_neg, add_comm] using this⟩)
  invFun p :=
    ⟨QuotientAddGroup.mk (Quotient.out p.1.val + (Quotient.out p.2).val), by
      obtain ⟨s, hs, hsc⟩ := p.1.property
      refine ⟨Quotient.out p.1.val + (Quotient.out p.2).val, ?_, rfl⟩
      have hc : Quotient.out p.1.val - s ∈ L' := by
        have := QuotientAddGroup.eq.mp
          ((QuotientAddGroup.out_eq' p.1.val).trans hsc.symm)
        have h2 := L'.neg_mem this
        simpa [sub_eq_add_neg, add_comm] using h2
      have hcs : Quotient.out p.1.val ∈ S := mem_of_sub_mem hS hs hc
      exact hS _ hcs _ (Quotient.out p.2).property⟩
  left_inv x := by
    apply Subtype.ext
    simp only
    set x0 := Quotient.out x.val
    set c := (QuotientAddGroup.mk x0 : V ⧸ L')
    set y : L' := Quotient.out (QuotientAddGroup.mk
      (⟨x0 - Quotient.out c, _⟩ : L') : L' ⧸ L.addSubgroupOf L')
    have hy : (QuotientAddGroup.mk y : L' ⧸ L.addSubgroupOf L') =
        QuotientAddGroup.mk ⟨x0 - Quotient.out c, _⟩ := QuotientAddGroup.out_eq' _
    have hmem := QuotientAddGroup.eq.mp hy
    rw [AddSubgroup.mem_addSubgroupOf] at hmem
    have hx : (QuotientAddGroup.mk x0 : V ⧸ L) = x.val := QuotientAddGroup.out_eq' _
    refine Eq.trans ?_ hx
    apply QuotientAddGroup.eq.mpr
    have : -(Quotient.out c + y.val) + x0 = -(y.val) + (x0 - Quotient.out c) := by abel
    rw [this]
    simpa using hmem
  right_inv p := by
    obtain ⟨⟨c, hc⟩, z⟩ := p
    set w := Quotient.out c + (Quotient.out z).val
    set w0 := Quotient.out (QuotientAddGroup.mk w : V ⧸ L)
    have hw : (QuotientAddGroup.mk w0 : V ⧸ L) = QuotientAddGroup.mk w := QuotientAddGroup.out_eq' _
    have hwL : -w0 + w ∈ L := QuotientAddGroup.eq.mp hw
    have hcw : (QuotientAddGroup.mk w0 : V ⧸ L') = c := by
      have h1 : (QuotientAddGroup.mk w0 : V ⧸ L') = QuotientAddGroup.mk w :=
        QuotientAddGroup.eq.mpr (h hwL)
      rw [h1]
      have h2 : (QuotientAddGroup.mk w : V ⧸ L') = QuotientAddGroup.mk (Quotient.out c) := by
        apply QuotientAddGroup.eq.mpr
        have : -w + Quotient.out c = -(Quotient.out z).val := by simp only [w]; abel
        rw [this]
        exact L'.neg_mem (Quotient.out z).property
      rw [h2, QuotientAddGroup.out_eq']
    refine Prod.ext (Subtype.ext ?_) ?_
    · exact hcw
    · conv_rhs => rw [← QuotientAddGroup.out_eq' z]
      apply QuotientAddGroup.eq.mpr
      rw [AddSubgroup.mem_addSubgroupOf]
      have hco : Quotient.out (QuotientAddGroup.mk w0 : V ⧸ L') = Quotient.out c := by rw [hcw]
      change -(w0 - Quotient.out (QuotientAddGroup.mk w0 : V ⧸ L')) + (Quotient.out z).val ∈ L
      rw [hco]
      have : -(w0 - Quotient.out c) + (Quotient.out z).val = -w0 + w := by simp only [w]; abel
      rw [this]
      exact hwL

/-- **Fiber counting.** -/
theorem card_image_mod (L L' : AddSubgroup V) (h : L ≤ L') (S : Set V)
    (hS : ∀ s ∈ S, ∀ l ∈ L', s + l ∈ S) :
    Nat.card ((QuotientAddGroup.mk : V → V ⧸ L) '' S) =
      Nat.card ((QuotientAddGroup.mk : V → V ⧸ L') '' S) * L.relIndex L' := by
  rw [Nat.card_congr (fiberEquiv L L' h S hS), Nat.card_prod]
  rfl

end TernaryPeriodPolynomials.HeckeEigen.Satake
