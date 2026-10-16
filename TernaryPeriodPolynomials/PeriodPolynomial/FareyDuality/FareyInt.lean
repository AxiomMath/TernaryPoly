module

public import Mathlib.Tactic
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Interval.Set.Group
public import Mathlib.Algebra.Order.Monoid.Submonoid
public import Mathlib.Algebra.Order.Ring.Interval
public import Mathlib.CategoryTheory.Adjunction.Limits
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
public import Mathlib.Lean.Meta.Basic
public import Mathlib.Lean.Meta.KAbstractPositions
public import Mathlib.Lean.Meta.Tactic.Rewrite
public import Mathlib.Lean.PrettyPrinter.Delaborator
public import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
public import Mathlib.NumberTheory.MulChar.Lemmas
public import Mathlib.RingTheory.Finiteness.Lattice
public import Mathlib.RingTheory.FreeCommRing
public import Mathlib.RingTheory.SimpleRing.Matrix
public import Mathlib.RingTheory.Valuation.IsTrivialOn
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Topology.Algebra.Module.UniformConvergence
public import Mathlib.Topology.Algebra.SeparationQuotient.Section
public import Mathlib.Topology.Order.AtTopBotIxx
public import Mathlib.Topology.WithTopology

@[expose] public section


/-!
# Integer inequalities for the Farey tree

Formalized by Claude Sonnet 5.5.

Elementary facts about pairs of integral plane vectors `a, b` with `det(a, b) = ±1` and the `ℓ¹` norm `N1`:
unimodular pairs are never in strictly opposite coordinate quadrants (`unimodular_no_opposite`); in a common
quadrant the norm is additive (`N1_add_of_quadrant`) and the longer vector dominates coordinatewise
(`quadrant_dominates`); a pair with all coordinate products zero consists of coordinate unit vectors
(`quadrant_central`).  Used to prove that the dual Farey tree has a rank function with unique descending edge.
-/

namespace TernaryPeriodPolynomials.Argument.FareyTree

/-- The `ℓ¹` norm of an integral vector in the plane. -/
def N1 (a0 a1 : ℤ) : ℤ := |a0| + |a1|

/-- Determinant. -/
def det2 (a0 a1 b0 b1 : ℤ) : ℤ := a0 * b1 - a1 * b0

theorem N1_nonneg (a0 a1 : ℤ) : 0 ≤ N1 a0 a1 := by unfold N1; positivity

theorem unimodular_no_opposite (a0 a1 b0 b1 : ℤ) (h : det2 a0 a1 b0 b1 = 1 ∨ det2 a0 a1 b0 b1 = -1) :
    ¬ (a0 * b0 > 0 ∧ a1 * b1 < 0) ∧ ¬ (a0 * b0 < 0 ∧ a1 * b1 > 0) := by
  simp only [det2] at h
  constructor
  · rintro ⟨h1, h2⟩
    rcases lt_trichotomy a0 0 with ha | ha | ha <;> rcases lt_trichotomy b0 0 with hb | hb | hb <;>
    rcases lt_trichotomy a1 0 with hc | hc | hc <;> rcases lt_trichotomy b1 0 with hd | hd | hd <;>
    first | (exfalso; nlinarith) | (rcases h with h | h <;> nlinarith)
  · rintro ⟨h1, h2⟩
    rcases lt_trichotomy a0 0 with ha | ha | ha <;> rcases lt_trichotomy b0 0 with hb | hb | hb <;>
    rcases lt_trichotomy a1 0 with hc | hc | hc <;> rcases lt_trichotomy b1 0 with hd | hd | hd <;>
    first | (exfalso; nlinarith) | (rcases h with h | h <;> nlinarith)

/-- In a common closed quadrant the norm is additive. -/
theorem N1_add_of_quadrant (a0 a1 b0 b1 : ℤ) (h0 : 0 ≤ a0 * b0) (h1 : 0 ≤ a1 * b1) :
    N1 (a0 + b0) (a1 + b1) = N1 a0 a1 + N1 b0 b1 := by
  unfold N1
  have e : ∀ x y : ℤ, 0 ≤ x * y → |x + y| = |x| + |y| := by
    intro x y h
    rcases le_total 0 x with hx | hx <;> rcases le_total 0 y with hy | hy
    · rw [abs_of_nonneg hx, abs_of_nonneg hy, abs_of_nonneg (add_nonneg hx hy)]
    · have hz : x * y = 0 := le_antisymm (mul_nonpos_of_nonneg_of_nonpos hx hy) h
      rcases mul_eq_zero.mp hz with h' | h'
      · subst h'; simp
      · subst h'; simp
    · have hz : x * y = 0 := le_antisymm (mul_nonpos_of_nonpos_of_nonneg hx hy) h
      rcases mul_eq_zero.mp hz with h' | h'
      · subst h'; simp
      · subst h'; simp
    · rw [abs_of_nonpos hx, abs_of_nonpos hy, abs_of_nonpos (add_nonpos hx hy)]; ring
  rw [e a0 b0 h0, e a1 b1 h1]
  ring

/-- In a common closed quadrant the norm of the difference is the sum of the differences of the
absolute values of the coordinates. -/
theorem N1_sub_of_quadrant (a0 a1 b0 b1 : ℤ) (h0 : 0 ≤ a0 * b0) (h1 : 0 ≤ a1 * b1) :
    N1 (a0 - b0) (a1 - b1) = |(|a0| - |b0|)| + |(|a1| - |b1|)| := by
  unfold N1
  have e : ∀ x y : ℤ, 0 ≤ x * y → |x - y| = |(|x| - |y|)| := by
    intro x y h
    rcases le_total 0 x with hx | hx <;> rcases le_total 0 y with hy | hy
    · rw [abs_of_nonneg hx, abs_of_nonneg hy]
    · have hz : x * y = 0 := le_antisymm (mul_nonpos_of_nonneg_of_nonpos hx hy) h
      rcases mul_eq_zero.mp hz with h' | h'
      · subst h'; simp
      · subst h'; simp
    · have hz : x * y = 0 := le_antisymm (mul_nonpos_of_nonpos_of_nonneg hx hy) h
      rcases mul_eq_zero.mp hz with h' | h'
      · subst h'; simp
      · subst h'; simp
    · rw [abs_of_nonpos hx, abs_of_nonpos hy, ← abs_neg (x - y)]
      congr 1
      ring
  rw [e a0 b0 h0, e a1 b1 h1]

/-- A unimodular pair in a common quadrant, all of whose coordinate products vanish, consists of
two coordinate unit vectors. -/
theorem quadrant_central (a0 a1 b0 b1 : ℤ) (hd : det2 a0 a1 b0 b1 = 1 ∨ det2 a0 a1 b0 b1 = -1)
    (h0 : a0 * b0 = 0) (h1 : a1 * b1 = 0) : N1 a0 a1 = 1 ∧ N1 b0 b1 = 1 := by
  have unit : ∀ x y : ℤ, (x * y = 1 ∨ x * y = -1) → |x| = 1 ∧ |y| = 1 := by
    intro x y h
    have h' : |x| * |y| = 1 := by
      rw [← abs_mul]; rcases h with h | h <;> rw [h] <;> simp
    exact ⟨Int.eq_one_of_mul_eq_one_right (abs_nonneg _) h',
      Int.eq_one_of_mul_eq_one_left (abs_nonneg _) h'⟩
  simp only [det2] at hd
  unfold N1
  rcases mul_eq_zero.mp h0 with e0 | e0 <;> rcases mul_eq_zero.mp h1 with e1 | e1
  · subst e0 e1; simp at hd
  · subst e0 e1
    have : (a1 * b0 = 1 ∨ a1 * b0 = -1) := by
      rcases hd with hd | hd
      · right; linarith
      · left; linarith
    obtain ⟨u, v⟩ := unit _ _ this
    simp [u, v]
  · subst e0 e1
    obtain ⟨u, v⟩ := unit a0 b1 (by simpa using hd)
    simp [u, v]
  · subst e0 e1; simp at hd

/-- Strict triangle inequality in a common quadrant unless the product vanishes in every coordinate. -/
theorem N1_sub_lt (a0 a1 b0 b1 : ℤ) (h0 : 0 ≤ a0 * b0) (h1 : 0 ≤ a1 * b1)
    (h : a0 * b0 ≠ 0 ∨ a1 * b1 ≠ 0) : N1 (a0 - b0) (a1 - b1) < N1 a0 a1 + N1 b0 b1 := by
  rw [N1_sub_of_quadrant a0 a1 b0 b1 h0 h1]
  unfold N1
  have key : ∀ x y : ℤ, 0 ≤ x * y → |(|x| - |y|)| ≤ |x| + |y| := by
    intro x y _
    rw [abs_le]; constructor <;> linarith [abs_nonneg x, abs_nonneg y]
  have strict : ∀ x y : ℤ, 0 ≤ x * y → x * y ≠ 0 → |(|x| - |y|)| < |x| + |y| := by
    intro x y hxy hne
    have hx : x ≠ 0 := left_ne_zero_of_mul hne
    have hy : y ≠ 0 := right_ne_zero_of_mul hne
    have hx' : 0 < |x| := abs_pos.mpr hx
    have hy' : 0 < |y| := abs_pos.mpr hy
    rw [abs_lt]; constructor <;> linarith
  rcases h with h | h
  · have := strict a0 b0 h0 h
    have := key a1 b1 h1
    linarith
  · have := strict a1 b1 h1 h
    have := key a0 b0 h0
    linarith

/-- Euclidean step: a unimodular pair in a common quadrant, the longer one dominates coordinatewise. -/
theorem quadrant_dominates (a0 a1 b0 b1 : ℤ) (hd : det2 a0 a1 b0 b1 = 1 ∨ det2 a0 a1 b0 b1 = -1)
    (h0 : 0 ≤ a0 * b0) (h1 : 0 ≤ a1 * b1) (hn : N1 b0 b1 ≤ N1 a0 a1) (ha : 2 ≤ N1 a0 a1) :
    |b0| ≤ |a0| ∧ |b1| ≤ |a1| := by
  simp only [det2, N1] at *
  rcases le_total 0 a0 with h | h <;> rcases le_total 0 a1 with h' | h' <;>
  rcases le_total 0 b0 with k | k <;> rcases le_total 0 b1 with k' | k' <;>
  simp only [abs_of_nonneg, abs_of_nonpos, *] at hn ha ⊢ <;>
  rcases hd with hd | hd <;>
  constructor <;> nlinarith

/-- In a non-central unimodular pair in a common quadrant, the difference is shorter than the longer
vector. -/
theorem N1_sub_lt_max (a0 a1 b0 b1 : ℤ) (hd : det2 a0 a1 b0 b1 = 1 ∨ det2 a0 a1 b0 b1 = -1)
    (h0 : 0 ≤ a0 * b0) (h1 : 0 ≤ a1 * b1) (ha : 1 ≤ N1 a0 a1) (hb : 1 ≤ N1 b0 b1)
    (hnc : ¬ (N1 a0 a1 = 1 ∧ N1 b0 b1 = 1)) :
    N1 (a0 - b0) (a1 - b1) < max (N1 a0 a1) (N1 b0 b1) := by
  rcases le_total (N1 b0 b1) (N1 a0 a1) with hle | hle
  · have h2 : 2 ≤ N1 a0 a1 := by
      by_contra hcon
      exact hnc ⟨by omega, by omega⟩
    obtain ⟨d0, d1⟩ := quadrant_dominates a0 a1 b0 b1 hd h0 h1 hle h2
    have e0 : |(|a0| - |b0|)| = |a0| - |b0| := abs_of_nonneg (by linarith)
    have e1 : |(|a1| - |b1|)| = |a1| - |b1| := abs_of_nonneg (by linarith)
    rw [N1_sub_of_quadrant a0 a1 b0 b1 h0 h1, e0, e1, max_eq_left hle]
    unfold N1 at *
    linarith
  · have h2 : 2 ≤ N1 b0 b1 := by
      by_contra hcon
      exact hnc ⟨by omega, by omega⟩
    have hd' : det2 b0 b1 a0 a1 = 1 ∨ det2 b0 b1 a0 a1 = -1 := by
      unfold det2 at *; rcases hd with hd | hd
      · right; linarith
      · left; linarith
    obtain ⟨d0, d1⟩ := quadrant_dominates b0 b1 a0 a1 hd' (by linarith [mul_comm a0 b0])
      (by linarith [mul_comm a1 b1]) hle h2
    have e0 : |(|a0| - |b0|)| = |b0| - |a0| := by rw [abs_of_nonpos (by linarith)]; ring
    have e1 : |(|a1| - |b1|)| = |b1| - |a1| := by rw [abs_of_nonpos (by linarith)]; ring
    rw [N1_sub_of_quadrant a0 a1 b0 b1 h0 h1, e0, e1, max_eq_right hle]
    unfold N1 at *
    linarith

end TernaryPeriodPolynomials.Argument.FareyTree
