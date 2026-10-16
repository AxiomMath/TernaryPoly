module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Algebra.QuadraticDiscriminant
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
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


/-! Weighted quadratic integral estimates for local regularizer kernels. -/
namespace TernaryPoly.WeightedIntegralSquare
open MeasureTheory
variable {X F : Type*} [MeasurableSpace X] {μ : Measure X}
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Weighted Cauchy-Schwarz in square form, without divisions or square-root integrability. -/
theorem integral_square_le (w f : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    (h0 : Integrable w μ) (h1 : Integrable (fun x => w x * f x) μ)
    (h2 : Integrable (fun x => w x * f x ^ 2) μ) :
    (∫ x, w x * f x ∂μ) ^ 2 ≤ (∫ x, w x ∂μ) * (∫ x, w x * f x ^ 2 ∂μ) := by
  have hq (t : ℝ) : 0 ≤ (∫ x, w x ∂μ) * (t * t) +
      (-2 * ∫ x, w x * f x ∂μ) * t + ∫ x, w x * f x ^ 2 ∂μ := by
    have hp : 0 ≤ ∫ x, w x * (t - f x) ^ 2 ∂μ :=
      integral_nonneg (fun x => mul_nonneg (hw x) (sq_nonneg (t - f x)))
    have he : (fun x => w x * (t - f x) ^ 2) =
        fun x => (t * t) * w x - (2 * t) * (w x * f x) + w x * f x ^ 2 := by
      funext x
      ring
    rw [he, integral_add ((h0.const_mul (t * t)).sub' (h1.const_mul (2 * t))) h2,
      integral_sub (h0.const_mul (t * t)) (h1.const_mul (2 * t)), integral_const_mul, integral_const_mul] at hp
    nlinarith
  have hdisc := discrim_le_zero hq
  unfold discrim at hdisc
  nlinarith

/-- The corresponding vector-valued weighted integral estimate. -/
theorem norm_integral_smul_square_le (w : X → ℝ) (f : X → F) (hw : ∀ x, 0 ≤ w x)
    (h0 : Integrable w μ) (h1 : Integrable (fun x => w x * ‖f x‖) μ)
    (h2 : Integrable (fun x => w x * ‖f x‖ ^ 2) μ) :
    ‖∫ x, w x • f x ∂μ‖ ^ 2 ≤
      (∫ x, w x ∂μ) * (∫ x, w x * ‖f x‖ ^ 2 ∂μ) := by
  have hn : ‖∫ x, w x • f x ∂μ‖ ≤ ∫ x, w x * ‖f x‖ ∂μ := by
    calc
      _ ≤ ∫ x, ‖w x • f x‖ ∂μ := norm_integral_le_integral_norm _
      _ = _ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun x => by dsimp only; rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hw x)])
  have hs := integral_square_le w (fun x => ‖f x‖) hw h0 h1 h2
  have hnorm := norm_nonneg (∫ x, w x • f x ∂μ)
  nlinarith

end TernaryPoly.WeightedIntegralSquare
