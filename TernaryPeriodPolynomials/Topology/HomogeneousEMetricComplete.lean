module

public import Mathlib.Topology.MetricSpace.Isometry
public import Mathlib.Topology.EMetricSpace.Basic
public import Mathlib.Topology.Compactness.LocallyCompact
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
public import Mathlib.Order.Filter.AtTopBot.Map
public import Mathlib.Tactic.Basify.Attr
public import Mathlib.Topology.WithTopology

@[expose] public section


/-! Locally compact homogeneous extended metric spaces are complete. -/
namespace TernaryPoly.HomogeneousEMetricComplete

open Filter Set EMetric
open scoped Topology ENNReal

/-- A compact neighborhood can be translated to contain a tail of every Cauchy sequence. -/
theorem complete_of_transitive_isometries {X : Type*} [EMetricSpace X] [LocallyCompactSpace X]
    (htrans : ∀ x y : X, ∃ g : X ≃ᵢ X, g x = y) : CompleteSpace X := by
  apply EMetric.complete_of_cauchySeq_tendsto
  intro u hu
  obtain ⟨K, hK, hKn⟩ := exists_compact_mem_nhds (u 0)
  obtain ⟨ε, hε, hball⟩ := EMetric.mem_nhds_iff.mp hKn
  obtain ⟨N, hN⟩ := EMetric.cauchySeq_iff.mp hu ε hε
  obtain ⟨g, hg⟩ := htrans (u 0) (u N)
  have htail : ∀ᶠ n in atTop, u n ∈ g '' K := by
    filter_upwards [eventually_ge_atTop N] with n hn
    refine ⟨g.symm (u n), hball ?_, g.apply_symm_apply _⟩
    change edist (g.symm (u n)) (u 0) < ε
    have he : edist (g.symm (u n)) (u 0) = edist (u n) (u N) := by
      calc
        _ = edist (g (g.symm (u n))) (g (u 0)) := (g.isometry_toFun _ _).symm
        _ = _ := by rw [g.apply_symm_apply, hg]
    rw [he]
    exact hN n hn N le_rfl
  obtain ⟨x, _, hx⟩ := (hK.image g.continuous).isComplete (map u atTop) hu
    (le_principal_iff.mpr htail)
  exact ⟨x, hx⟩

end TernaryPoly.HomogeneousEMetricComplete
