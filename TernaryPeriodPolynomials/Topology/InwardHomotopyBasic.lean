module

public import Mathlib.Topology.Homotopy.Equiv
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Module.End
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Ring.Pow
public import Mathlib.Data.Fintype.Option
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


noncomputable section
namespace TernaryPoly.InwardHomotopy
open scoped unitInterval
variable {X : Type*} [TopologicalSpace X]

/-- A local inward deformation preserves the designated interior; an endpoint that remains
outside the interior was fixed. This last condition makes finite compositions cover the boundary. -/
structure LocalDeformation (U : Set X) where
  homotopy : C(I × X, X)
  zero : ∀ x, homotopy (0,x)=x
  preserves : ∀ t x, x∈U → homotopy (t,x)∈U
  endpoint_fixed : ∀ x, homotopy (1,x)∉U → homotopy (1,x)=x

end TernaryPoly.InwardHomotopy
