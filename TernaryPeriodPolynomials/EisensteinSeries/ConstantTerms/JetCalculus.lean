module

public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.BigOperators.Associated
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Monoid.Submonoid
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.Analysis.Asymptotics.Theta
public import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
public import Mathlib.Data.Fintype.Order
public import Mathlib.Data.List.Enum
public import Mathlib.Data.Nat.Choose.Cast
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


/-!
# The abstract jet bound for a triple product (Leibniz and Faà di Bruno)

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergenceC4

open scoped ContDiff

/-! ### The abstract calculus lemma (Leibniz and Faà di Bruno) -/

/-- The combinatorial constant of the jet bound of a triple product `(φ ∘ u) * θ * w`. -/
def jetConst (N : ℕ) (D : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (N + 1), ∑ a ∈ Finset.range (i + 1),
    (N.choose i : ℝ) * (i.choose a : ℝ) * ((a.factorial : ℝ) * D ^ a)

theorem jetConst_nonneg (N : ℕ) {D : ℝ} (hD : 0 ≤ D) : 0 ≤ jetConst N D := by
  unfold jetConst
  positivity

theorem triple_jet_bound {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set E} (hU : IsOpen U) {q : E} (hq : q ∈ U)
    {H : Set ℂ} (hH : IsOpen H) {u : E → ℂ} (hu : ContDiffOn ℝ ∞ u U) (huH : Set.MapsTo u U H)
    {φ : ℂ → ℂ} (hφ : ContDiffOn ℝ ∞ φ H) {θ w : E → ℂ} (hθ : ContDiffOn ℝ ∞ θ U)
    (hw : ContDiffOn ℝ ∞ w U) (N : ℕ) {c D T Y : ℝ} (hD0 : 0 ≤ D) (hT0 : 0 ≤ T)
    (hc : ∀ i, i ≤ N → ‖iteratedFDerivWithin ℝ i φ H (u q)‖ ≤ c)
    (hD : ∀ i, 1 ≤ i → i ≤ N → ‖iteratedFDerivWithin ℝ i u U q‖ ≤ D ^ i)
    (hT : ∀ i, i ≤ N → ‖iteratedFDerivWithin ℝ i θ U q‖ ≤ T)
    (hY : ∀ i, i ≤ N → ‖iteratedFDerivWithin ℝ i w U q‖ ≤ Y) :
    ‖iteratedFDerivWithin ℝ N (fun x => φ (u x) * θ x * w x) U q‖ ≤
      jetConst N D * c * T * Y := by
  have hUq : UniqueDiffOn ℝ U := hU.uniqueDiffOn
  have hHq : UniqueDiffOn ℝ H := hH.uniqueDiffOn
  have hc0 : 0 ≤ c := (norm_nonneg _).trans (hc 0 (Nat.zero_le _))
  have h1 : ContDiffOn ℝ ∞ (fun x => φ (u x)) U := hφ.comp hu huH
  have h12 : ContDiffOn ℝ ∞ (fun x => φ (u x) * θ x) U := h1.mul hθ
  -- bound for the composite
  have hA : ∀ a, a ≤ N → ‖iteratedFDerivWithin ℝ a (fun x => φ (u x)) U q‖ ≤
      (a.factorial : ℝ) * c * D ^ a := by
    intro a ha
    have := norm_iteratedFDerivWithin_comp_le (g := φ) (f := u) (n := a) (N := ∞) hφ hu
      (by exact_mod_cast le_top) hHq hUq huH hq (C := c) (D := D)
      (fun i hi => hc i (hi.trans ha)) (fun i hi1 hi2 => hD i hi1 (hi2.trans ha))
    exact this
  have hP : ∀ i, i ≤ N → ‖iteratedFDerivWithin ℝ i (fun x => φ (u x) * θ x) U q‖ ≤
      ∑ a ∈ Finset.range (i + 1), (i.choose a : ℝ) * ((a.factorial : ℝ) * c * D ^ a) * T := by
    intro i hi
    refine (norm_iteratedFDerivWithin_mul_le h1 hθ hUq hq (by exact_mod_cast le_top)).trans ?_
    refine Finset.sum_le_sum fun a ha => ?_
    have haN : a ≤ N := (Nat.lt_succ_iff.1 (Finset.mem_range.1 ha)).trans hi
    have hiaN : i - a ≤ N := (Nat.sub_le _ _).trans hi
    exact mul_le_mul (mul_le_mul_of_nonneg_left (hA a haN) (by positivity))
      (hT _ hiaN) (norm_nonneg _) (by positivity)
  refine (norm_iteratedFDerivWithin_mul_le h12 hw hUq hq (by exact_mod_cast le_top)).trans ?_
  have : jetConst N D * c * T * Y = ∑ i ∈ Finset.range (N + 1), (N.choose i : ℝ) *
      (∑ a ∈ Finset.range (i + 1), (i.choose a : ℝ) * ((a.factorial : ℝ) * c * D ^ a) * T) * Y := by
    unfold jetConst
    rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    ring
  rw [this]
  refine Finset.sum_le_sum fun i hi => ?_
  have hiN : i ≤ N := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  have hNi : N - i ≤ N := Nat.sub_le _ _
  exact mul_le_mul (mul_le_mul_of_nonneg_left (hP i hiN) (by positivity)) (hY _ hNi)
    (norm_nonneg _) (by positivity)

end TernaryPeriodPolynomials.Argument.ConvergenceC4
