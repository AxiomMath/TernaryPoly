module

public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.GroupWithZero.Indicator
public import Mathlib.Algebra.Module.Basic
public import Mathlib.Algebra.Module.Submodule.EqLocus
public import Mathlib.Algebra.Module.Torsion.Field
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.Control.Basic
public import Mathlib.Data.Fintype.Option
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

@[expose] public section


namespace TernaryPoly.OrdinaryFaceRadical

/-- A kernel-containment criterion transports equality through two genuine linear maps. -/
theorem linearMap_eq_of_kernel {V W U : Type} [AddCommGroup V] [AddCommGroup W]
    [AddCommGroup U] [Module ℚ V] [Module ℚ W] [Module ℚ U]
    (F : V →ₗ[ℚ] W) (E : V →ₗ[ℚ] U) (hker : ∀ z,F z=0 → E z=0)
    (c d : V) (h : F c=F d) : E c=E d := by
  apply sub_eq_zero.mp
  rw [←E.map_sub]
  apply hker
  rw [F.map_sub,h,sub_self]

end TernaryPoly.OrdinaryFaceRadical
