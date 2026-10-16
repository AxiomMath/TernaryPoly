module

public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.Module.Torsion.Field
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.Data.Fintype.Order
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
public import Mathlib.Topology.WithTopology

@[expose] public section


noncomputable section
namespace TernaryPoly.FreeActionLinearization

universe v w t
variable (G : Type v) (T : Type t) (X : Type w)
variable [Group G] [TopologicalSpace T] [TopologicalSpace X]
variable [MulAction G X] [ContinuousConstSMul G X] [IsCancelSMul G X] [Nonempty T]

/-- Evaluation at any domain point detects freeness of the actual pointwise action. -/
theorem continuousMap_smul_right_cancel (g h : G) (f : C(T,X))
    (heq : g • f=h • f) : g=h := by
  let t : T := Classical.choice ‹Nonempty T›
  exact IsCancelSMul.right_cancel g h (f t)
    (congrArg (fun F : C(T,X) => F t) heq)

/-- Continuous maps from any nonempty space inherit a free pointwise action. -/
instance continuousMap_isCancelSMul : IsCancelSMul G C(T,X) where
  right_cancel' := continuousMap_smul_right_cancel G T X

end TernaryPoly.FreeActionLinearization
