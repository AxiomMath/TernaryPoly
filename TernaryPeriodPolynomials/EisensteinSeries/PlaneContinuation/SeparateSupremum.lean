module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
public import Mathlib.Algebra.BigOperators.Associated
public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Interval.Set.Group
public import Mathlib.Algebra.Order.Monoid.Canonical.Basic
public import Mathlib.Algebra.Order.Monoid.Submonoid
public import Mathlib.Algebra.Order.Ring.Interval
public import Mathlib.Algebra.Ring.Hom.InjSurj
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
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.Tactic.Basify.Attr
public import Mathlib.Topology.Order.AtTopBotIxx
public import Mathlib.Topology.WithTopology

@[expose] public section


open MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.SeparateSupremum

variable {First Second Space : Type*}

def bound (function : First → Second → Space → ℂ) (firsts : Set First) (seconds : Set Second) (point : Space) : ℝ :=
  (⨆ first : firsts, ⨆ second : seconds, ENNReal.ofReal ‖function first.val second.val point‖).toReal

theorem nonnegative (function : First → Second → Space → ℂ) (firsts : Set First) (seconds : Set Second) (point : Space) :
    0 ≤ bound function firsts seconds point := ENNReal.toReal_nonneg

theorem bounded (function : First → Second → Space → ℂ) (firsts : Set First) (seconds : Set Second)
    (point : Space) (constant : ℝ) (constantNonnegative : 0 ≤ constant)
    (bounds : ∀ first ∈ firsts, ∀ second ∈ seconds, ‖function first second point‖ ≤ constant) :
    bound function firsts seconds point ≤ constant := by
  have inequality : (⨆ first : firsts, ⨆ second : seconds, ENNReal.ofReal ‖function first.val second.val point‖) ≤ ENNReal.ofReal constant :=
    iSup_le (fun first => iSup_le (fun second => ENNReal.ofReal_le_ofReal (bounds first.val first.property second.val second.property)))
  simpa only [bound, ENNReal.toReal_ofReal constantNonnegative] using
    ENNReal.toReal_mono ENNReal.ofReal_ne_top inequality

theorem dominates (function : First → Second → Space → ℂ) (firsts : Set First) (seconds : Set Second)
    (point : Space) (bounded : ∃ constant : ℝ, ∀ first ∈ firsts, ∀ second ∈ seconds, ‖function first second point‖ ≤ constant)
    (first : First) (firstMembership : first ∈ firsts) (second : Second) (secondMembership : second ∈ seconds) :
    ‖function first second point‖ ≤ bound function firsts seconds point := by
  obtain ⟨constant, bounds⟩ := bounded
  have finite : (⨆ first : firsts, ⨆ second : seconds, ENNReal.ofReal ‖function first.val second.val point‖) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (iSup_le (fun first => iSup_le (fun second => ENNReal.ofReal_le_ofReal (bounds first.val first.property second.val second.property))))
  have inequality : ENNReal.ofReal ‖function first second point‖ ≤
      ⨆ first : firsts, ⨆ second : seconds, ENNReal.ofReal ‖function first.val second.val point‖ :=
    le_iSup_of_le ⟨first, firstMembership⟩ (le_iSup_of_le ⟨second, secondMembership⟩ le_rfl)
  simpa only [bound, ENNReal.toReal_ofReal (norm_nonneg _)] using ENNReal.toReal_mono finite inequality

theorem measurable [MeasurableSpace Space] [TopologicalSpace First] [TopologicalSpace Second]
    [SecondCountableTopology First] [SecondCountableTopology Second]
    (function : First → Second → Space → ℂ) (firsts : Set First) (seconds : Set Second)
    (measurable : ∀ first ∈ firsts, ∀ second ∈ seconds, Measurable (function first second))
    (firstContinuous : ∀ second ∈ seconds, ∀ point, ContinuousOn (fun first => function first second point) firsts)
    (secondContinuous : ∀ first ∈ firsts, ∀ point, ContinuousOn (fun second => function first second point) seconds) :
    Measurable (bound function firsts seconds) := by
  apply Measurable.ennreal_toReal
  have innerMeasurable (first : firsts) :
      Measurable (fun point => ⨆ second : seconds, ENNReal.ofReal ‖function first.val second.val point‖) := by
    have result := measurable_iSup_of_lowerSemicontinuous
      (f := fun second : seconds => fun point => ENNReal.ofReal ‖function first.val second.val point‖)
      (fun second => (measurable first.val first.property second.val second.property).norm.ennreal_ofReal)
      (fun point => (ENNReal.continuous_ofReal.comp ((secondContinuous first.val first.property point).domRestrict).norm).lowerSemicontinuous)
    convert result using 1
    funext point
    symm
    exact iSup_apply
  have result := measurable_iSup_of_lowerSemicontinuous innerMeasurable
    (fun point => lowerSemicontinuous_iSup (fun second : seconds =>
      (ENNReal.continuous_ofReal.comp ((firstContinuous second.val second.property point).domRestrict).norm).lowerSemicontinuous))
  convert result using 1
  funext point
  symm
  exact iSup_apply

theorem congr (function : First → Second → Space → ℂ) (firsts : Set First) (seconds : Set Second) (left right : Space)
    (equal : ∀ first ∈ firsts, ∀ second ∈ seconds, function first second left = function first second right) :
    bound function firsts seconds left = bound function firsts seconds right := by
  unfold bound
  congr 1
  apply iSup_congr
  intro first
  apply iSup_congr
  intro second
  rw [equal first.val first.property second.val second.property]

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.SeparateSupremum
