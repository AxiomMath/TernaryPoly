module

public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Measure.OpenPos
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


open MeasureTheory

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem invariant_ae_zero_of_fundamental_domain
    {G X Y : Type*} [Group G] [MulAction G X] [Countable G] [MeasurableSpace X]
    [MeasurableConstSMul G X] [Zero Y] {measure : Measure X} [SMulInvariantMeasure G X measure]
    {domain : Set X} (measurable : MeasurableSet domain) (fundamental : IsFundamentalDomain G domain measure)
    {function : X → Y} (invariant : ∀ element : G, ∀ point, function (element • point) = function point)
    (zero : ∀ᵐ point ∂measure.restrict domain, function point = 0) :
    ∀ᵐ point ∂measure, function point = 0 := by
  have domain_zero := (ae_restrict_iff' measurable).mp zero
  have translated : ∀ element : G, ∀ᵐ point ∂measure,
      element • point ∈ domain → function (element • point) = 0 := fun element =>
    (measurePreserving_smul element measure).quasiMeasurePreserving.ae domain_zero
  filter_upwards [ae_all_iff.mpr translated, fundamental.ae_covers] with point vanishes covered
  obtain ⟨element, member⟩ := covered
  simpa only [invariant] using vanishes element member

theorem continuous_invariant_zero_of_fundamental_domain
    {G X Y : Type*} [Group G] [MulAction G X] [Countable G] [MeasurableSpace X]
    [MeasurableConstSMul G X] [Zero Y] [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    {measure : Measure X} [SMulInvariantMeasure G X measure] [measure.IsOpenPosMeasure]
    {domain : Set X} (measurable : MeasurableSet domain) (fundamental : IsFundamentalDomain G domain measure)
    {function : X → Y} (continuous : Continuous function)
    (invariant : ∀ element : G, ∀ point, function (element • point) = function point)
    (zero : ∀ᵐ point ∂measure.restrict domain, function point = 0) : function = 0 := by
  apply (continuous.ae_eq_iff_eq measure continuous_const).mp
  exact invariant_ae_zero_of_fundamental_domain measurable fundamental invariant zero

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
