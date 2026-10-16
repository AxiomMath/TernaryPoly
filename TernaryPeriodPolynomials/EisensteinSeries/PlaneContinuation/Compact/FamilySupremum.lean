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

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.CompactFamilySupremum

variable {Space : Type*}

def bound (function : ℂ → Space → ℂ) (parameters : Set ℂ) (point : Space) : ℝ :=
  (⨆ parameter : parameters, ENNReal.ofReal ‖function parameter.val point‖).toReal

theorem nonnegative (function : ℂ → Space → ℂ) (parameters : Set ℂ) (point : Space) :
    0 ≤ bound function parameters point := ENNReal.toReal_nonneg

theorem bounded (function : ℂ → Space → ℂ) (parameters : Set ℂ) (point : Space)
    (constant : ℝ) (nonnegative : 0 ≤ constant)
    (bounded : ∀ parameter ∈ parameters, ‖function parameter point‖ ≤ constant) :
    bound function parameters point ≤ constant := by
  have inequality : (⨆ parameter : parameters, ENNReal.ofReal ‖function parameter.val point‖) ≤ ENNReal.ofReal constant :=
    iSup_le (fun parameter => ENNReal.ofReal_le_ofReal (bounded parameter.val parameter.property))
  simpa only [bound, ENNReal.toReal_ofReal nonnegative] using
    ENNReal.toReal_mono ENNReal.ofReal_ne_top inequality

theorem dominates (function : ℂ → Space → ℂ) (parameters : Set ℂ) (compact : IsCompact parameters)
    (continuous : ∀ point, ContinuousOn (fun parameter => function parameter point) parameters)
    (point : Space) (parameter : ℂ) (membership : parameter ∈ parameters) :
    ‖function parameter point‖ ≤ bound function parameters point := by
  obtain ⟨constant, bounded⟩ := compact.exists_bound_of_continuousOn (continuous point)
  have finite : (⨆ parameter : parameters, ENNReal.ofReal ‖function parameter.val point‖) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (iSup_le (fun parameter => ENNReal.ofReal_le_ofReal (bounded parameter.val parameter.property)))
  have inequality := le_iSup (fun parameter : parameters => ENNReal.ofReal ‖function parameter.val point‖) ⟨parameter, membership⟩
  simpa only [bound, ENNReal.toReal_ofReal (norm_nonneg _)] using ENNReal.toReal_mono finite inequality

theorem measurable [MeasurableSpace Space] (function : ℂ → Space → ℂ) (parameters : Set ℂ)
    (measurable : ∀ parameter ∈ parameters, Measurable (function parameter))
    (continuous : ∀ point, ContinuousOn (fun parameter => function parameter point) parameters) :
    Measurable (bound function parameters) := by
  apply Measurable.ennreal_toReal
  have result := measurable_iSup_of_lowerSemicontinuous
    (f := fun parameter : parameters => fun point => ENNReal.ofReal ‖function parameter.val point‖)
    (fun parameter => (measurable parameter.val parameter.property).norm.ennreal_ofReal)
    (fun point => (ENNReal.continuous_ofReal.comp (continuous point |>.domRestrict).norm).lowerSemicontinuous)
  have equality : (⨆ parameter : parameters, fun point => ENNReal.ofReal ‖function parameter.val point‖) =
      (fun point => ⨆ parameter : parameters, ENNReal.ofReal ‖function parameter.val point‖) := by
    funext point
    exact iSup_apply
  rw [equality] at result
  exact result

theorem congr (function : ℂ → Space → ℂ) (parameters : Set ℂ) (first second : Space)
    (equal : ∀ parameter ∈ parameters, function parameter first = function parameter second) :
    bound function parameters first = bound function parameters second := by
  unfold bound
  congr 1
  apply iSup_congr
  intro parameter
  rw [equal parameter.val parameter.property]

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.CompactFamilySupremum
