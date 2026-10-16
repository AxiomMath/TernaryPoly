module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.GroupWithZero.Indicator
public import Mathlib.Algebra.Module.Torsion.Field
public import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
public import Mathlib.Algebra.MonoidAlgebra.Support
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Ring.Hom.InjSurj
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

@[expose] public section


/-!
# A binomial identity for the edge of the line seed (LS14a)

For a sequence `G`, writing `A = ∑_{j ≤ n} (-1)^{n-j} C(n,j) G_j X^j Y^{n-j}` and `B = ∑_{j ≤ n} (-1)^{n-j} C(n,j) G_{j+1} X^j Y^{n-j}`,
`Y A - X B = -∑_{i ≤ n+1} (-1)^{n+1-i} C(n+1,i) G_i X^i Y^{n+1-i}` (Pascal's rule).  This is the contraction `Y α - X β` of the lower radical coordinate applied to the
values of the seed cocycle on the two radical generators.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LineSeed

variable {R : Type*} [CommRing R]

/-- `∑_{j ≤ n} C(n,j) (-1)^{n-j} G_j x^j y^{n-j}` for a sequence `G`, in any commutative ring. -/
def combSum (n : ℕ) (G : ℕ → R) (x y : R) : R :=
  ∑ j ∈ Finset.range (n + 1), ((n.choose j : R) * (-1) ^ (n - j) * G j) * x ^ j * y ^ (n - j)

theorem contraction_identity (n : ℕ) (G : ℕ → R) (x y : R) :
    y * combSum n G x y - x * combSum n (fun j => G (j + 1)) x y = -combSum (n + 1) G x y := by
  -- the terms of the right-hand side
  let h : ℕ → R := fun i => ((n.choose i : R) * (-1) ^ (n + 1 - i) * G i) * x ^ i * y ^ (n + 1 - i)
  have hA : y * combSum n G x y = -∑ i ∈ Finset.range (n + 1), h i := by
    unfold combSum
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have e1 : n + 1 - i = (n - i) + 1 := by omega
    simp only [h, e1, pow_succ]
    ring
  have hsum : ∑ i ∈ Finset.range (n + 2), h i = ∑ i ∈ Finset.range (n + 1), h i := by
    rw [Finset.sum_range_succ]
    have : h (n + 1) = 0 := by simp [h, Nat.choose_succ_self]
    rw [this, add_zero]
  have hsum' : ∑ i ∈ Finset.range (n + 2), h i = ∑ j ∈ Finset.range (n + 1), h (j + 1) + h 0 :=
    Finset.sum_range_succ' h (n + 1)
  -- Pascal
  have hR : combSum (n + 1) G x y =
      ∑ j ∈ Finset.range (n + 1), (((n.choose j : R) * (-1) ^ (n - j) * G (j + 1)) * x ^ (j + 1) * y ^ (n - j)
        + h (j + 1)) + h 0 := by
    unfold combSum
    rw [Finset.sum_range_succ' _ (n + 1)]
    congr 1
    · refine Finset.sum_congr rfl fun j hj => ?_
      simp only [h]
      rw [Nat.choose_succ_succ, Nat.cast_add]
      have : n + 1 - (j + 1) = n - j := by omega
      rw [this]
      ring
    · simp [h]
  have hB : x * combSum n (fun j => G (j + 1)) x y =
      ∑ j ∈ Finset.range (n + 1), ((n.choose j : R) * (-1) ^ (n - j) * G (j + 1)) * x ^ (j + 1) * y ^ (n - j) := by
    unfold combSum
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hA, hB, hR, Finset.sum_add_distrib]
  have := hsum.symm.trans hsum'
  linear_combination (-1 : R) * this

end TernaryPeriodPolynomials.Argument.LineSeed
