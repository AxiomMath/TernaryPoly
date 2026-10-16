module

public import Mathlib.Topology.Sequences
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Algebra.BigOperators.Associated
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Submonoid.Units
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
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Topology.Algebra.Module.UniformConvergence
public import Mathlib.Topology.Algebra.SeparationQuotient.Section
public import Mathlib.Topology.WithTopology

@[expose] public section


/-! One dense-input sequence approximates a regularizer and both of its bounded derivatives. -/
namespace TernaryPoly.DenseRegularizerApproximation
open Filter
open scoped Topology

variable {V E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem exists_simultaneous_sequence (i : V → E) (hi : DenseRange i)
    (r : V → V) (d : V → F) (a : V → G)
    (R : E →L[ℝ] E) (B : E →L[ℝ] F) (C : E →L[ℝ] G)
    (hR : ∀ v, R (i v) = i (r v))
    (hB : ∀ v, B (i v) = d (r v))
    (hC : ∀ v, C (i v) = a (r v)) (x : E) :
    ∃ u : ℕ → V,
      Tendsto (fun j => i (u j)) atTop (𝓝 (R x)) ∧
      Tendsto (fun j => d (u j)) atTop (𝓝 (B x)) ∧
      Tendsto (fun j => a (u j)) atTop (𝓝 (C x)) := by
  obtain ⟨v, hv, hx⟩ := mem_closure_iff_seq_limit.mp (hi x)
  choose w hw using hv
  have hwx : Tendsto (fun j => i (w j)) atTop (𝓝 x) := by
    simpa only [hw] using hx
  refine ⟨fun j => r (w j), ?_, ?_, ?_⟩
  · simpa only [Function.comp_def, hR] using R.continuous.continuousAt.tendsto.comp hwx
  · simpa only [Function.comp_def, hB] using B.continuous.continuousAt.tendsto.comp hwx
  · simpa only [Function.comp_def, hC] using C.continuous.continuousAt.tendsto.comp hwx

end TernaryPoly.DenseRegularizerApproximation
