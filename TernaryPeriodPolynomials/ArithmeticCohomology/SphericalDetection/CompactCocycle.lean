module

public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Analysis.Complex.Basic
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

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {G E : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem integrableCocycle_average (measure : Measure G)
    [IsProbabilityMeasure measure] [measure.IsMulLeftInvariant]
    (action : G → E →L[ℂ] E) (cycle : G → E)
    (cocycle : ∀ first second, cycle (first * second) =
      cycle first + action first (cycle second))
    (integrable : Integrable cycle measure) (element : G) :
    cycle element = action element (-(∫ argument, cycle argument ∂measure)) -
      (-(∫ argument, cycle argument ∂measure)) := by
  have average : (∫ argument, cycle argument ∂measure) =
      cycle element + action element (∫ argument, cycle argument ∂measure) := by
    calc
      (∫ argument, cycle argument ∂measure) =
          ∫ argument, cycle (element * argument) ∂measure :=
        (integral_mul_left_eq_self cycle element).symm
      _ = ∫ argument, cycle element + action element (cycle argument) ∂measure := by
        congr 1
        funext argument
        exact cocycle element argument
      _ = _ := by
        rw [integral_add (integrable_const _) ((action element).integrable_comp integrable),
          integral_const, (action element).integral_comp_comm integrable]
        simp
  rw [map_neg]
  exact (eq_sub_iff_add_eq.mpr average.symm).trans (by abel)

theorem compactCocycle_average [TopologicalSpace G] [CompactSpace G]
    [OpensMeasurableSpace G] (measure : Measure G)
    [IsProbabilityMeasure measure] [measure.IsMulLeftInvariant]
    (action : G → E →L[ℂ] E) (cycle : G → E)
    (cocycle : ∀ first second, cycle (first * second) =
      cycle first + action first (cycle second))
    (continuous : Continuous cycle) (element : G) :
    cycle element = action element (-(∫ argument, cycle argument ∂measure)) -
      (-(∫ argument, cycle argument ∂measure)) :=
  integrableCocycle_average measure action cycle cocycle
    (continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace cycle)) element

end TernaryPeriodPolynomials.SphericalDetection.Helpers
