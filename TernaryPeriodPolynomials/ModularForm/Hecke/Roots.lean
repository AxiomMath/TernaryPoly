module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.Algebra.BigOperators.Associated
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Interval.Set.Group
public import Mathlib.Algebra.Order.Monoid.Submonoid
public import Mathlib.Algebra.Order.Ring.Interval
public import Mathlib.Algebra.Ring.Action.Pointwise.Set
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.Data.Finsupp.Antidiagonal
public import Mathlib.Data.Fintype.Order
public import Mathlib.Data.List.Enum
public import Mathlib.Data.Nat.GCD.BigOperators
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
public import Mathlib.Tactic.Basify.Attr
public import Mathlib.Tactic.ComputeDegree
public import Mathlib.Topology.Order.AtTopBotIxx
public import Mathlib.Topology.WithTopology

@[expose] public section


noncomputable section
namespace TernaryPoly.BinaryCuspHecke

/-- The finite root-of-unity filter, valid for every positive order. -/
theorem root_power_sum {p : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ p) (n : ℕ) :
    (∑ b : Fin p, (ζ ^ b.val) ^ n) = if p ∣ n then (p : ℂ) else 0 := by
  simp_rw [← pow_mul, Nat.mul_comm _ n, pow_mul]
  rw [Fin.sum_univ_eq_sum_range]
  by_cases hd : p ∣ n
  · simp [(hζ.pow_eq_one_iff_dvd n).mpr hd, hd]
  · rw [ite_eq_right hd]
    have hn : ζ ^ n - 1 ≠ 0 := sub_ne_zero.mpr (mt (hζ.pow_eq_one_iff_dvd n).mp hd)
    have he := geom_sum_mul (ζ ^ n) p
    have hp : (ζ ^ n) ^ p = 1 := by
      rw [← pow_mul, Nat.mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
    rw [hp, sub_self] at he
    exact (mul_eq_zero.mp he).resolve_right hn

/-- The explicit primitive p-th root used by the standard Hecke translations. -/
def root (p : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / p)

theorem root_primitive {p : ℕ} (hp : p ≠ 0) : IsPrimitiveRoot (root p) p :=
  Complex.isPrimitiveRoot_exp p hp

theorem root_power_sum_exp {p : ℕ} (hp : p ≠ 0) (n : ℕ) :
    (∑ b : Fin p, (root p ^ b.val) ^ n) = if p ∣ n then (p : ℂ) else 0 :=
  root_power_sum (root_primitive hp) n

end TernaryPoly.BinaryCuspHecke
