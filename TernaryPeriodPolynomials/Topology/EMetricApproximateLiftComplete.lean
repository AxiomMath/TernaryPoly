module

public import Mathlib.Topology.EMetricSpace.Basic
public import Mathlib.Topology.MetricSpace.Cauchy
public import Mathlib.Tactic
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Interval.Set.Group
public import Mathlib.Algebra.Order.Monoid.Submonoid
public import Mathlib.Algebra.Order.Ring.Interval
public import Mathlib.CategoryTheory.Adjunction.Limits
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
public import Mathlib.Lean.Meta.Basic
public import Mathlib.Lean.Meta.KAbstractPositions
public import Mathlib.Lean.Meta.Tactic.Rewrite
public import Mathlib.Lean.PrettyPrinter.Delaborator
public import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
public import Mathlib.NumberTheory.MulChar.Lemmas
public import Mathlib.RingTheory.Finiteness.Lattice
public import Mathlib.RingTheory.FreeCommRing
public import Mathlib.RingTheory.SimpleRing.Matrix
public import Mathlib.RingTheory.Valuation.IsTrivialOn
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Topology.Algebra.Module.UniformConvergence
public import Mathlib.Topology.Algebra.SeparationQuotient.Section
public import Mathlib.Topology.Order.AtTopBotIxx
public import Mathlib.Topology.WithTopology

@[expose] public section

/-! Completeness descends under a continuous map with arbitrarily close lifts. -/
namespace TernaryPoly.EMetricApproximateLiftComplete

open Filter
open scoped Topology ENNReal

/-- Lift controlled Cauchy sequences with summably small successive distances. -/
theorem complete_of_approximate_lifts {X Y : Type*} [EMetricSpace X] [EMetricSpace Y]
    [CompleteSpace X] (f : X → Y) (hf : Continuous f) (hsurj : Function.Surjective f)
    (hlift : ∀ x y r, edist (f x) y < r → ∃ x', f x' = y ∧ edist x x' < r) :
    CompleteSpace Y := by
  apply EMetric.complete_of_convergent_controlled_sequences (fun n => (1 : ℝ≥0∞) / 2 ^ n)
    (fun n => ENNReal.div_pos (by simp) (by finiteness))
  intro u hu
  obtain ⟨x0, hx0⟩ := hsurj (u 0)
  have step (n : ℕ) (x : {x : X // f x = u n}) :
      ∃ x' : {x : X // f x = u (n + 1)}, edist x.val x'.val < (1 : ℝ≥0∞) / 2 ^ n := by
    obtain ⟨x', hx', hd⟩ := hlift x.val (u (n + 1)) ((1 : ℝ≥0∞) / 2 ^ n)
      (by rw [x.property]; exact hu n n (n + 1) le_rfl (Nat.le_succ n))
    exact ⟨⟨x', hx'⟩, hd⟩
  let v : ∀ n, {x : X // f x = u n} :=
    fun n => Nat.rec (motive := fun n => {x : X // f x = u n}) ⟨x0, hx0⟩
      (fun n x => (step n x).choose) n
  have hvstep (n : ℕ) : edist (v n).val (v (n + 1)).val ≤ (1 : ℝ≥0∞) / 2 ^ n :=
    (step n (v n)).choose_spec.le
  have hv : CauchySeq (fun n => (v n).val) :=
    cauchySeq_of_edist_le_geometric_two 1 (by simp) hvstep
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hv
  refine ⟨f x, ?_⟩
  have h := hf.continuousAt.tendsto.comp hx
  simpa only [Function.comp_def, (v _).property] using h

end TernaryPoly.EMetricApproximateLiftComplete
