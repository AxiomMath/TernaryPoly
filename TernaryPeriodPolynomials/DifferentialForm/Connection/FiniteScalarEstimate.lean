module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Control.Basic
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

@[expose] public section


/-! Finite scalar estimates for quantitative partition gluing. -/
noncomputable section
namespace TernaryPoly.PolynomialFormConnection
open Finset
variable {ι : Type*} [Fintype ι]

/-- Nonnegative weights of total mass at most one preserve a uniform absolute-value bound. -/
theorem abs_weighted_sum_le (p a : ι → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i ≤ 1)
    (ha : ∀ i, p i ≠ 0 → |a i| ≤ C) : |∑ i, p i * a i| ≤ C := by
  calc
    _ ≤ ∑ i, |p i * a i| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, p i * C := by
      apply sum_le_sum
      intro i _
      by_cases hi : p i = 0
      · simp [hi]
      · rw [abs_mul, abs_of_nonneg (hp i)]
        exact mul_le_mul_of_nonneg_left (ha i hi) (hp i)
    _ = (∑ i, p i) * C := (sum_mul _ _ _).symm
    _ ≤ C := by nlinarith

/-- The value error of a finite partition average is controlled by the local errors. -/
theorem abs_partition_error_le (p g : ι → ℝ) (c : ℝ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i ≤ 1) (hc : (∑ i, p i) * c = c)
    (hg : ∀ i, p i ≠ 0 → |g i - c| ≤ δ) : |(∑ i, p i * g i) - c| ≤ δ := by
  have he : (∑ i, p i * g i) - c = ∑ i, p i * (g i - c) := by
    simp only [mul_sub, sum_sub_distrib, ← sum_mul, hc]
  rw [he]
  exact abs_weighted_sum_le p (fun i => g i - c) hδ hp hs hg

/-- Small local errors absorb all finite partition-derivative terms. -/
theorem abs_partition_derivative_le (p g a b : ι → ℝ) (c : ℝ) {L δ D V : ℝ}
    (hL : 0 ≤ L) (hδ : 0 ≤ δ) (hD : 0 ≤ D) (hV : 0 ≤ V)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i ≤ 1)
    (ha : ∀ i, p i ≠ 0 → |a i| ≤ L * V)
    (hb : ∀ i, |b i| ≤ D * V)
    (hg : ∀ i, b i ≠ 0 → |g i - c| ≤ δ) (hc : c * (∑ i, b i) = 0) :
    |∑ i, (p i * a i + g i * b i)| ≤ (L + (Fintype.card ι : ℝ) * δ * D) * V := by
  have hmain := abs_weighted_sum_le p a (mul_nonneg hL hV) hp hs ha
  have he : ∑ i, g i * b i = ∑ i, (g i - c) * b i := by
    simp only [sub_mul, sum_sub_distrib, ← mul_sum, hc, sub_zero]
  have herr : |∑ i, (g i - c) * b i| ≤ (Fintype.card ι : ℝ) * (δ * (D * V)) := by
    calc
      _ ≤ ∑ i, |(g i - c) * b i| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : ι, δ * (D * V) := by
        apply sum_le_sum
        intro i _
        by_cases hi : b i = 0
        · simp only [hi, mul_zero, abs_zero]
          positivity
        · rw [abs_mul]
          exact mul_le_mul (hg i hi) (hb i) (abs_nonneg _) hδ
      _ = _ := by simp
  rw [sum_add_distrib, he]
  calc
    _ ≤ |∑ i, p i * a i| + |∑ i, (g i - c) * b i| := abs_add_le _ _
    _ ≤ L * V + (Fintype.card ι : ℝ) * (δ * (D * V)) := add_le_add hmain herr
    _ = _ := by ring

end TernaryPoly.PolynomialFormConnection
