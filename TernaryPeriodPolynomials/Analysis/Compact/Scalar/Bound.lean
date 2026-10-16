module

public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Ring.Pow
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
public import Mathlib.Tactic.Basify.Attr
public import Mathlib.Topology.WithTopology

@[expose] public section


/-! A genuine finite uniform norm bound for a continuous compact scalar function. -/
namespace TernaryPoly.CompactScalarBound
variable {E : Type*} [TopologicalSpace E] [Nonempty E]

theorem exists_bound (f : E → ℝ) (hf : Continuous f) (hc : HasCompactSupport f) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖f x‖ ≤ M := by
  obtain ⟨M,hM⟩ := (hc.isCompact_range hf).isBounded.exists_norm_le
  have hb (x : E) : ‖f x‖ ≤ M := hM _ ⟨x,rfl⟩
  exact ⟨M,(norm_nonneg (f (Classical.arbitrary E))).trans (hb _),hb⟩

end TernaryPoly.CompactScalarBound
