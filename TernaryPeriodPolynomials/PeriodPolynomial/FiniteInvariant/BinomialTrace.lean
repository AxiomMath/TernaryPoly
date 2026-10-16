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

noncomputable section
namespace TernaryPoly.BinaryFiniteInvariant

/-- The alternating binomial sum governing the rotation trace. -/
def rotationSum (n : ℕ) : ℚ :=
  ∑ i ∈ Finset.range (n+1), (-1 : ℚ)^i * ((n-i).choose i : ℚ)

@[simp] theorem rotationSum_zero : rotationSum 0=1 := by norm_num [rotationSum,Finset.sum_range_succ]
@[simp] theorem rotationSum_one : rotationSum 1=1 := by norm_num [rotationSum,Finset.sum_range_succ]

theorem rotationSum_shift (n : ℕ) :
    rotationSum (n+1) = 1-∑ j ∈ Finset.range (n+1), (-1 : ℚ)^j * ((n-j).choose (j+1) : ℚ) := by
  unfold rotationSum
  rw [Finset.sum_range_succ']
  simp only [Nat.add_sub_add_right,pow_succ,Nat.sub_zero,Nat.choose_zero_right,Nat.cast_one,
    pow_zero,mul_one]
  rw [sub_eq_add_neg,←Finset.sum_neg_distrib,add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Pascal's identity gives the uniform order-two recurrence. -/
theorem rotationSum_recurrence (n : ℕ) :
    rotationSum (n+2)=rotationSum (n+1)-rotationSum n := by
  have h := rotationSum_shift (n+1)
  rw [Finset.sum_range_succ] at h
  simp only [Nat.sub_self,Nat.choose_zero_succ,Nat.cast_zero,mul_zero,add_zero] at h
  have he : (∑ j ∈ Finset.range (n+1), (-1 : ℚ)^j * (((n+1-j).choose (j+1)) : ℚ)) =
      rotationSum n + ∑ j ∈ Finset.range (n+1), (-1 : ℚ)^j * ((n-j).choose (j+1) : ℚ) := by
    unfold rotationSum
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    have hjn : j≤n := by simpa using Finset.mem_range.mp hj
    rw [show n+1-j=(n-j)+1 by omega,Nat.choose_succ_succ',Nat.cast_add,mul_add]
  rw [he] at h
  have hs := rotationSum_shift n
  linarith

theorem rotationSum_add_three (n : ℕ) : rotationSum (n+3) = -rotationSum n := by
  have h := rotationSum_recurrence n
  have h' := rotationSum_recurrence (n+1)
  linarith

theorem rotationSum_add_six (n : ℕ) : rotationSum (n+6) = rotationSum n := by
  calc
    rotationSum (n+6) = -rotationSum (n+3) := rotationSum_add_three (n+3)
    _ = rotationSum n := by rw [rotationSum_add_three,neg_neg]

theorem rotationSum_mod_six (n : ℕ) : rotationSum n = rotationSum (n%6) := by
  by_cases h : n<6
  · rw [Nat.mod_eq_of_lt h]
  · have hn : n-6<n := by omega
    rw [show n=(n-6)+6 by omega,rotationSum_add_six,rotationSum_mod_six (n-6)]
    congr 1
    omega
termination_by n

end TernaryPoly.BinaryFiniteInvariant
