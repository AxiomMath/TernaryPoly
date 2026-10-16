module

public import Mathlib.Topology.Algebra.Module.LinearPMap
public import Mathlib.Analysis.Normed.Module.Basic
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


/-! The minimal closed operator is contained in every actual closed extension. -/
namespace TernaryPoly.HilbertClosedOperator
open scoped LinearPMap
variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedSpace ℝ E] [NormedSpace ℝ F]

/-- The graph closure is contained in every closed extension. -/
theorem closure_le (S T : E →ₗ.[ℝ] F) (hT : T.IsClosed) (hST : S ≤ T) :
    S.closure ≤ T := by
  apply LinearPMap.le_of_le_graph
  rw [← (hT.isClosable.leIsClosable hST).graph_closure_eq_closure_graph]
  exact Submodule.topologicalClosure_minimal _ (LinearPMap.le_graph_of_le hST) hT

end TernaryPoly.HilbertClosedOperator
