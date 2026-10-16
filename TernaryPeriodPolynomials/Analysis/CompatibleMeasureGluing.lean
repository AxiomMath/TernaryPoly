module

public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.Algebra.BigOperators.Associated
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
public import Mathlib.Topology.Order.AtTopBotIxx
public import Mathlib.Topology.WithTopology

@[expose] public section

/-! Gluing genuine local measures along a countable measurable cover. -/
noncomputable section
namespace TernaryPoly.CompatibleMeasureGluing

open MeasureTheory Set
variable {X : Type*} [MeasurableSpace X]

/-- Disjoint pieces of a countable atlas avoid multiple counting. -/
def glued (U : ℕ → Set X) (μ : ℕ → Measure X) : Measure X :=
  Measure.sum fun i => (μ i).restrict (disjointed U i)

/-- Pairwise compatible local measures restrict to the exact prescribed measure on each chart. -/
theorem glued_restrict (U : ℕ → Set X) (hU : ∀ i, MeasurableSet (U i))
    (hcover : (⋃ i, U i) = univ) (μ : ℕ → Measure X)
    (hcompat : ∀ i j, (μ i).restrict (U j) = (μ j).restrict (U i)) (j : ℕ) :
    (glued U μ).restrict (U j) = μ j := by
  unfold glued
  rw [Measure.restrict_sum _ (hU j)]
  have hpiece (i : ℕ) : ((μ i).restrict (disjointed U i)).restrict (U j) =
      (μ j).restrict (disjointed U i) := by
    rw [Measure.restrict_comm (hU j), hcompat i j,
      Measure.restrict_restrict_of_subset (disjointed_le U i)]
  simp_rw [hpiece]
  rw [← Measure.restrict_iUnion (disjoint_disjointed U) (MeasurableSet.disjointed hU),
    iUnion_disjointed, hcover, Measure.restrict_univ]

/-- The glued measure is independent of the disjointization and is uniquely determined locally. -/
theorem unique (U : ℕ → Set X)
    (hcover : (⋃ i, U i) = univ) (μ ν : Measure X)
    (h : ∀ i, μ.restrict (U i) = ν.restrict (U i)) : μ = ν := by
  have hh : μ.restrict (⋃ i, U i) = ν.restrict (⋃ i, U i) :=
    Measure.restrict_iUnion_congr.mpr h
  simpa only [hcover, Measure.restrict_univ] using hh

end TernaryPoly.CompatibleMeasureGluing
