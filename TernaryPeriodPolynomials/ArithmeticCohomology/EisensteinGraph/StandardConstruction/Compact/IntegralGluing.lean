module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Pointwise.Set.Card
public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Interval.Set.Group
public import Mathlib.Algebra.Order.Monoid.Canonical.Basic
public import Mathlib.Algebra.Order.Monoid.Submonoid
public import Mathlib.Algebra.Order.Ring.Interval
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Data.Fintype.Order
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
public import Mathlib.SetTheory.Cardinal.ENNReal
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Tactic.Basify.Attr
public import Mathlib.Topology.Order.AtTopBotIxx
public import Mathlib.Topology.WithTopology

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.CompactIntegralGluing

theorem integral_mem_of_finite_cover {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (measure : Measure X) (function : X → E) (integrable : Integrable function measure)
    (space : Submodule ℂ E) {Index : Type*} (indices : Finset Index)
    (cover : Index → Set X) (measurable : ∀ index, MeasurableSet (cover index))
    (localIntegral : ∀ index ∈ indices, ∀ subset, MeasurableSet subset →
      subset ⊆ cover index → (∫ x in subset, function x ∂measure) ∈ space)
    (subset : Set X) (subsetMeasurable : MeasurableSet subset)
    (covered : subset ⊆ ⋃ index ∈ indices, cover index) :
    (∫ x in subset, function x ∂measure) ∈ space := by
  classical
  induction indices using Finset.induction_on generalizing subset with
  | empty =>
    have empty : subset = ∅ := by simpa using covered
    simp [empty]
  | @insert index indices absent inductionHypothesis =>
    have split : subset = (subset ∩ cover index) ∪ (subset \ cover index) := by
      ext x
      simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_sdiff]
      tauto
    have remaining : subset \ cover index ⊆ ⋃ other ∈ indices, cover other := by
      intro x membership
      have member := covered membership.1
      simp only [Finset.mem_insert, Set.iUnion_iUnion_eq_or_left, Set.mem_union] at member
      exact member.resolve_left membership.2
    rw [split, setIntegral_union Set.disjoint_sdiff_inter.symm
      (subsetMeasurable.diff (measurable index))
      integrable.integrableOn integrable.integrableOn]
    exact space.add_mem
      (localIntegral index (Finset.mem_insert_self _ _) _
        (subsetMeasurable.inter (measurable index)) Set.inter_subset_right)
      (inductionHypothesis (fun other member =>
        localIntegral other (Finset.mem_insert_of_mem member)) _
          (subsetMeasurable.diff (measurable index)) remaining)

theorem integral_mem_of_local {X E : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] [CompactSpace X]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (measure : Measure X) (function : X → E) (integrable : Integrable function measure)
    (space : Submodule ℂ E)
    (localIntegral : ∀ x : X, ∃ neighborhood : Set X, IsOpen neighborhood ∧
      x ∈ neighborhood ∧ ∀ subset, MeasurableSet subset → subset ⊆ neighborhood →
        (∫ point in subset, function point ∂measure) ∈ space) :
    (∫ x, function x ∂measure) ∈ space := by
  classical
  choose cover openness contains localProperty using localIntegral
  obtain ⟨indices, covers⟩ := isCompact_univ.elim_finite_subcover cover openness (by
    intro x _
    exact Set.mem_iUnion.mpr ⟨x, contains x⟩)
  have member := integral_mem_of_finite_cover measure function integrable space
    indices cover (fun x => (openness x).measurableSet)
    (fun index _ => localProperty index) Set.univ MeasurableSet.univ covers
  simpa only [Measure.restrict_univ] using member

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.CompactIntegralGluing
