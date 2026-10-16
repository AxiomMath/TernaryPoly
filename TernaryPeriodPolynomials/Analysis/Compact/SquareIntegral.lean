module

public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Tactic.Linarith
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


/-! Genuine square-integrability and cutoff bounds for compact continuous functions. -/
namespace TernaryPoly.CompactSquareIntegral
open MeasureTheory
variable {E F : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] {μ : Measure E} [IsFiniteMeasureOnCompacts μ]

theorem integrable_norm_square (f : E → F) (hf : Continuous f) (hc : HasCompactSupport f) :
    Integrable (fun x => ‖f x‖ ^ 2) μ :=
  (hf.norm.pow 2).integrable_of_hasCompactSupport (by
    simpa only [pow_two, Pi.mul_apply] using hc.norm.mul_right (f' := fun x => ‖f x‖))

variable [NormedSpace ℝ F]

theorem cutoff_square_le (φ : E → ℝ) (z : E → F) (hφ : Continuous φ)
    (hcφ : HasCompactSupport φ) (hz : Continuous z)
    (hzi : Integrable (fun x => ‖z x‖ ^ 2) μ) (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ x, ‖φ x‖ ≤ M) :
    ∫ x, ‖φ x • z x‖ ^ 2 ∂μ ≤ M^2 * ∫ x, ‖z x‖ ^ 2 ∂μ := by
  rw [← integral_const_mul]
  apply integral_mono (integrable_norm_square _ (hφ.smul hz) hcφ.smul_right) (hzi.const_mul _)
  intro x
  change ‖φ x • z x‖ ^ 2 ≤ M^2 * ‖z x‖^2
  rw [norm_smul (φ x) (z x), mul_pow]
  exact mul_le_mul_of_nonneg_right (by nlinarith [hb x, norm_nonneg (φ x)]) (sq_nonneg _)

end TernaryPoly.CompactSquareIntegral
