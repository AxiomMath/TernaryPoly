module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Algebra.BigOperators.Associated
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.Analysis.Asymptotics.Theta
public import Mathlib.Analysis.Calculus.Deriv.AffineMap
public import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
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
public import Mathlib.Topology.WithTopology

@[expose] public section


/-! Genuine global coefficient bounds supplied by compact C1 support. -/
namespace TernaryPoly.CompactFirstOrderCoefficients
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Compact C1 coefficients give the actual Lipschitz, directional derivative and zeroth-order
bounds needed by the Friedrichs estimate, without a separate coefficient-bound premise. -/
theorem exists_bounds (a b : E → ℝ) (v : E) (ha : ContDiff ℝ 1 a) (hb : Continuous b)
    (hca : HasCompactSupport a) (hcb : HasCompactSupport b) :
    ∃ L A B : ℝ, 0 ≤ L ∧ 0 ≤ A ∧ 0 ≤ B ∧
      (∀ x y, ‖a x - a y‖ ≤ L * ‖x-y‖) ∧
      (∀ y, ‖fderiv ℝ a y v‖ ≤ A) ∧ (∀ y, ‖b y‖ ≤ B) := by
  obtain ⟨L, hL⟩ := ((hca.fderiv ℝ).isCompact_range (ha.continuous_fderiv one_ne_zero)).isBounded.exists_norm_le
  obtain ⟨B, hB⟩ := (hcb.isCompact_range hb).isBounded.exists_norm_le
  have hLa (y : E) : ‖fderiv ℝ a y‖ ≤ L := hL _ ⟨y, rfl⟩
  have hBb (y : E) : ‖b y‖ ≤ B := hB _ ⟨y, rfl⟩
  have hL0 : 0 ≤ L := (norm_nonneg (fderiv ℝ a 0)).trans (hLa 0)
  have hB0 : 0 ≤ B := (norm_nonneg (b 0)).trans (hBb 0)
  have hlip : LipschitzWith ⟨L, hL0⟩ a :=
    lipschitzWith_of_nnnorm_fderiv_le (ha.differentiable one_ne_zero) (fun y => hLa y)
  refine ⟨L, L * ‖v‖, B, hL0, mul_nonneg hL0 (norm_nonneg _), hB0, ?_, ?_, hBb⟩
  · intro x y
    have hh := hlip.dist_le_mul x y
    change dist (a x) (a y) ≤ L * dist x y at hh
    simpa only [dist_eq_norm] using hh
  · intro y
    exact ((fderiv ℝ a y).le_opNorm v).trans (mul_le_mul_of_nonneg_right (hLa y) (norm_nonneg _))

end TernaryPoly.CompactFirstOrderCoefficients
