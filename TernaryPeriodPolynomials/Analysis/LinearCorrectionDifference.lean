module

public import Mathlib.Algebra.Module.LinearMap.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Control.Basic
public import Mathlib.Data.String.Defs
public import Mathlib.Lean.Elab.InfoTree
public import Mathlib.Lean.Elab.Tactic.Basic
public import Mathlib.Lean.Elab.Tactic.Meta
public import Mathlib.Lean.Expr.Basic
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

namespace TernaryPoly.LinearCorrection
variable {R A B C : Type*} [Ring R] [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
  [Module R A] [Module R B] [Module R C]

theorem differential_difference (D : A →ₗ[R] B) (I : C →ₗ[R] B) (T : B)
    (f g : A) (a b : C) (hf : D f = T-I a) (hg : D g = T-I b) :
    D (g-f) = I (a-b) := by
  rw [map_sub, hg, hf, map_sub]
  abel

end TernaryPoly.LinearCorrection
