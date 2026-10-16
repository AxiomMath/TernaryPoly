module

public import Mathlib.Analysis.InnerProductSpace.LinearPMap
public import Mathlib.Topology.MetricSpace.Antilipschitz
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Interval.Set.Group
public import Mathlib.Algebra.Order.Ring.Interval
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.Data.List.Enum
public import Mathlib.Data.Nat.NthRoot.Defs
public import Mathlib.Data.String.Defs
public import Mathlib.GroupTheory.QuotientGroup.ModEq
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
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
public import Mathlib.RingTheory.Finiteness.Lattice
public import Mathlib.RingTheory.SimpleRing.Matrix
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Tactic.Basify.Attr
public import Mathlib.Topology.Order.AtTopBotIxx
public import Mathlib.Topology.WithTopology

@[expose] public section


noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace E] [CompleteSpace F]

theorem closedGraph_second_range (graph : Submodule ℂ (E × F)) (closed : IsClosed (graph : Set (E × F)))
    (bound : NNReal) (estimate : ∀ pair ∈ graph, ‖pair.1‖ ≤ bound * ‖pair.2‖) :
    IsClosed (Set.range (fun pair : graph => pair.val.2)) := by
  let : CompleteSpace graph := closed.completeSpace_coe
  let projection : graph →L[ℂ] F := (ContinuousLinearMap.snd ℂ E F).comp graph.subtypeL
  have anti : AntilipschitzWith (max bound 1) projection := by
    apply AntilipschitzWith.of_le_mul_dist
    intro first second
    have inequality := estimate (first.val - second.val) (graph.sub_mem first.property second.property)
    simp only [dist_eq_norm]
    change max ‖first.val.1 - second.val.1‖ ‖first.val.2 - second.val.2‖ ≤
      (max bound 1 : NNReal) * ‖first.val.2 - second.val.2‖
    apply max_le
    · exact inequality.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast le_max_left bound 1) (norm_nonneg _))
    · have scalar : (1 : ℝ) ≤ (max bound 1 : NNReal) := by exact_mod_cast le_max_right bound 1
      simpa only [one_mul] using mul_le_mul_of_nonneg_right scalar (norm_nonneg (first.val.2 - second.val.2))
  exact anti.isClosed_range projection.uniformContinuous

theorem closedLinearPMap_range (operator : E →ₗ.[ℂ] F) (closed : operator.IsClosed)
    (bound : NNReal) (estimate : ∀ vector : operator.domain, ‖vector.val‖ ≤ bound * ‖(operator vector : F)‖) :
    IsClosed (operator.toFun.range : Set F) := by
  have estimate_graph : ∀ pair ∈ operator.graph, ‖pair.1‖ ≤ bound * ‖pair.2‖ := by
    intro pair member
    obtain ⟨vector, first, second⟩ := operator.mem_graph_iff.mp member
    rw [← first, ← second]
    exact estimate vector
  have range_closed := closedGraph_second_range operator.graph closed bound estimate_graph
  have equality : Set.range (fun pair : operator.graph => pair.val.2) = (operator.toFun.range : Set F) := by
    ext value
    constructor
    · rintro ⟨pair, rfl⟩
      exact LinearPMap.mem_range_iff.mpr ⟨pair.val.1, pair.property⟩
    · intro member
      obtain ⟨first, pair_mem⟩ := LinearPMap.mem_range_iff.mp member
      exact ⟨⟨(first, value), pair_mem⟩, rfl⟩
  rw [← equality]
  exact range_closed

omit [CompleteSpace E] [CompleteSpace F] in
theorem closableLinearPMap_closure_bound (operator : E →ₗ.[ℂ] F) (closable : operator.IsClosable)
    (bound : NNReal) (estimate : ∀ vector : operator.domain, ‖vector.val‖ ≤ bound * ‖(operator vector : F)‖) :
    ∀ vector : operator.closure.domain, ‖vector.val‖ ≤ bound * ‖(operator.closure vector : F)‖ := by
  have estimate_graph : (operator.graph : Set (E × F)) ⊆ {pair | ‖pair.1‖ ≤ bound * ‖pair.2‖} := by
    intro pair member
    obtain ⟨vector, first, second⟩ := operator.mem_graph_iff.mp member
    change ‖pair.1‖ ≤ bound * ‖pair.2‖
    rw [← first, ← second]
    exact estimate vector
  have closed_bound : IsClosed {pair : E × F | ‖pair.1‖ ≤ bound * ‖pair.2‖} :=
    isClosed_le continuous_fst.norm (continuous_const.mul continuous_snd.norm)
  have closure_bound := closure_minimal estimate_graph closed_bound
  intro vector
  change (vector.val, (operator.closure vector : F)) ∈ {pair : E × F | ‖pair.1‖ ≤ bound * ‖pair.2‖}
  apply closure_bound
  change (vector.val, (operator.closure vector : F)) ∈ operator.graph.topologicalClosure
  rw [closable.graph_closure_eq_closure_graph]
  exact operator.closure.mem_graph vector

omit [CompleteSpace E] [CompleteSpace F] in
theorem closableLinearPMap_closure_constraints (operator : E →ₗ.[ℂ] F) (closable : operator.IsClosable)
    (source : Submodule ℂ E) (target : Submodule ℂ F)
    (source_closed : IsClosed (source : Set E)) (target_closed : IsClosed (target : Set F))
    (domain_mem : operator.domain ≤ source) (range_mem : ∀ vector : operator.domain, (operator vector : F) ∈ target)
    (vector : operator.closure.domain) : vector.val ∈ source ∧ (operator.closure vector : F) ∈ target := by
  have graph_mem : (operator.graph : Set (E × F)) ⊆ (source : Set E) ×ˢ (target : Set F) := by
    intro pair member
    obtain ⟨value, first, second⟩ := operator.mem_graph_iff.mp member
    change pair.1 ∈ source ∧ pair.2 ∈ target
    rw [← first, ← second]
    exact ⟨domain_mem value.property, range_mem value⟩
  have closure_mem := closure_minimal graph_mem (source_closed.prod target_closed)
  change (vector.val, (operator.closure vector : F)) ∈ (source : Set E) ×ˢ (target : Set F)
  apply closure_mem
  change (vector.val, (operator.closure vector : F)) ∈ operator.graph.topologicalClosure
  rw [closable.graph_closure_eq_closure_graph]
  exact operator.closure.mem_graph vector

theorem closableLinearPMap_closure_range_isClosed (operator : E →ₗ.[ℂ] F) (closable : operator.IsClosable)
    (bound : NNReal) (estimate : ∀ vector : operator.domain, ‖vector.val‖ ≤ bound * ‖(operator vector : F)‖) :
    IsClosed (operator.closure.toFun.range : Set F) :=
  closedLinearPMap_range operator.closure closable.closure_isClosed bound
    (closableLinearPMap_closure_bound operator closable bound estimate)

end TernaryPeriodPolynomials.SphericalDetection.Helpers
