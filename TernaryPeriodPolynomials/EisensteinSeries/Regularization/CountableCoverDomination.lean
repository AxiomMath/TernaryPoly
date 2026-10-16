module

public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Pointwise.Set.Card
public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Interval.Set.Group
public import Mathlib.Algebra.Order.Monoid.Canonical.Basic
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
public import Mathlib.SetTheory.Cardinal.ENNReal
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Tactic.Basify.Attr
public import Mathlib.Topology.Algebra.IsUniformGroup.Order
public import Mathlib.Topology.Order.AtTopBotIxx
public import Mathlib.Topology.WithTopology

@[expose] public section


open MeasureTheory Filter
open scoped ENNReal

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

noncomputable def weightedCoverMajorant {I X : Type*} (sets : I → Set X) (weights : I → ℝ≥0∞) (point : X) : ℝ≥0∞ :=
  ∑' index, (sets index).indicator (fun _ => weights index) point

theorem weightedCoverMajorant_measurable {I X : Type*} [Countable I] [MeasurableSpace X]
    (sets : I → Set X) (weights : I → ℝ≥0∞) (measurable : ∀ index, MeasurableSet (sets index)) :
    Measurable (weightedCoverMajorant sets weights) :=
  Measurable.tsum (fun index => measurable_const.indicator (measurable index))

theorem weightedCoverMajorant_lintegral {I X : Type*} [Countable I] [MeasurableSpace X]
    (sets : I → Set X) (weights : I → ℝ≥0∞) (measure : Measure X)
    (measurable : ∀ index, MeasurableSet (sets index)) :
    (∫⁻ point, weightedCoverMajorant sets weights point ∂measure) = ∑' index, weights index * measure (sets index) := by
  unfold weightedCoverMajorant
  rw [lintegral_tsum (fun index => (measurable_const.indicator (measurable index)).aemeasurable)]
  apply tsum_congr
  intro index
  rw [lintegral_indicator (measurable index), lintegral_const, Measure.restrict_apply_univ]

theorem weightedCoverMajorant_ge {I X : Type*} (sets : I → Set X) (weights : I → ℝ≥0∞)
    (index : I) {point : X} (member : point ∈ sets index) :
    weights index ≤ weightedCoverMajorant sets weights point := by
  simpa only [Set.indicator_of_mem member, weightedCoverMajorant] using
    (ENNReal.le_tsum (f := fun index => (sets index).indicator (fun _ => weights index) point) index)

theorem weightedCoverMajorant_integrable {I X : Type*} [Countable I] [MeasurableSpace X]
    (sets : I → Set X) (weights : I → ℝ≥0∞) (measure : Measure X)
    (measurable : ∀ index, MeasurableSet (sets index))
    (finite : (∑' index, weights index * measure (sets index)) < ⊤) :
    Integrable (fun point => (weightedCoverMajorant sets weights point).toReal) measure := by
  apply integrable_toReal_of_lintegral_ne_top (weightedCoverMajorant_measurable sets weights measurable).aemeasurable
  rw [weightedCoverMajorant_lintegral sets weights measure measurable]
  exact ne_of_lt finite

theorem weightedCoverMajorant_dominates {I X E : Type*} [Countable I] [MeasurableSpace X]
    [NormedAddCommGroup E] (sets : I → Set X) (weights : I → ℝ≥0∞) (measure : Measure X)
    (measurable : ∀ index, MeasurableSet (sets index)) (cover : (⋃ index, sets index) = Set.univ)
    (finite : (∑' index, weights index * measure (sets index)) < ⊤)
    {function : X → E} (bounded : ∀ index, ∀ point ∈ sets index, ENNReal.ofReal ‖function point‖ ≤ weights index) :
    ∀ᵐ point ∂measure, ‖function point‖ ≤ (weightedCoverMajorant sets weights point).toReal := by
  have finite_integral : (∫⁻ point, weightedCoverMajorant sets weights point ∂measure) ≠ ⊤ := by
    rw [weightedCoverMajorant_lintegral sets weights measure measurable]
    exact ne_of_lt finite
  filter_upwards [ae_lt_top (weightedCoverMajorant_measurable sets weights measurable) finite_integral] with point finite_point
  obtain ⟨index, member⟩ := Set.mem_iUnion.mp (show point ∈ ⋃ index, sets index by rw [cover]; trivial)
  exact (ENNReal.ofReal_le_iff_le_toReal (ne_of_lt finite_point)).mp
    ((bounded index point member).trans (weightedCoverMajorant_ge sets weights index member))

theorem tendsto_integral_of_countable_cover {I X T E : Type*} [Countable I] [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (sets : I → Set X) (weights : I → ℝ≥0∞)
    (measure : Measure X) (filter : Filter T) [filter.IsCountablyGenerated]
    (measurable_sets : ∀ index, MeasurableSet (sets index)) (cover : (⋃ index, sets index) = Set.univ)
    (finite : (∑' index, weights index * measure (sets index)) < ⊤)
    {family : T → X → E} {limit : X → E}
    (measurable : ∀ᶠ parameter in filter, AEStronglyMeasurable (family parameter) measure)
    (bounded : ∀ᶠ parameter in filter, ∀ index, ∀ point ∈ sets index,
      ENNReal.ofReal ‖family parameter point‖ ≤ weights index)
    (converges : ∀ᵐ point ∂measure, Tendsto (fun parameter => family parameter point) filter (nhds (limit point))) :
    Tendsto (fun parameter => ∫ point, family parameter point ∂measure) filter (nhds (∫ point, limit point ∂measure)) := by
  apply tendsto_integral_filter_of_dominated_convergence
    (fun point => (weightedCoverMajorant sets weights point).toReal) measurable
  · filter_upwards [bounded] with parameter bound
    exact weightedCoverMajorant_dominates sets weights measure measurable_sets cover finite bound
  · exact weightedCoverMajorant_integrable sets weights measure measurable_sets finite
  · exact converges

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
