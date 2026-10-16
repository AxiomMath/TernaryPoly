module

public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.Normed.Module.FiniteDimension
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


open MeasureTheory
open scoped ENNReal

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem absolute_series_pairing
    {I X : Type*} [Countable I] [MeasurableSpace X] (measure : Measure X)
    {family : I → X → ℂ} {test : X → ℂ}
    (measurable : ∀ index, AEStronglyMeasurable (family index) measure)
    (test_measurable : AEStronglyMeasurable test measure)
    (summable : ∀ point, Summable (fun index => family index point))
    (integrable : Integrable (fun point => (∑' index, ‖family index point‖) * ‖test point‖) measure) :
    (∑' index, ∫⁻ point, ‖family index point * test point‖ₑ ∂measure) < ⊤ ∧
      (∫ point, (∑' index, family index point) * test point ∂measure) =
        ∑' index, ∫ point, family index point * test point ∂measure := by
  have product_measurable (index : I) : AEStronglyMeasurable
      (fun point => family index point * test point) measure := (measurable index).mul test_measurable
  have identity (point : X) : (∑' index, ‖family index point * test point‖ₑ) =
      ‖(∑' index, ‖family index point‖) * ‖test point‖‖ₑ := by
    simp only [← ofReal_norm, norm_mul, norm_norm]
    rw [Real.norm_of_nonneg (tsum_nonneg (fun _ => norm_nonneg _))]
    rw [← tsum_mul_right]
    exact (ENNReal.ofReal_tsum_of_nonneg (fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
      ((summable point).norm.mul_right ‖test point‖)).symm
  have finite : (∑' index, ∫⁻ point, ‖family index point * test point‖ₑ ∂measure) < ⊤ := by
    rw [← lintegral_tsum (fun index => (product_measurable index).enorm)]
    simp_rw [identity]
    exact integrable.hasFiniteIntegral
  refine ⟨finite, ?_⟩
  simp_rw [← tsum_mul_right]
  exact integral_tsum product_measurable (ne_of_lt finite)

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
