module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
public import Lean.Elab.Tactic.Omega
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.GroupWithZero.Indicator
public import Mathlib.Algebra.Module.Torsion.Field
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
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Tactic.Basify.Attr
public import Mathlib.Tactic.ComputeDegree

@[expose] public section

open MvPolynomial

namespace TernaryPoly

/-- Multiplication by a homogeneous polynomial shifts homogeneous projection. -/
theorem homogeneousComponent_mul_homogeneous {σ : Type*} {R : Type*}
    [CommSemiring R] {p : MvPolynomial σ R} {m : ℕ}
    (hp : p.IsHomogeneous m) (q : MvPolynomial σ R) (n : ℕ) :
    homogeneousComponent (m+n) (p*q) = p*homogeneousComponent n q := by
  classical
  induction q using MvPolynomial.induction_on' with
  | monomial d r =>
    have hmono := isHomogeneous_monomial (d := d) r rfl
    rw [homogeneousComponent_of_mem (hp.mul hmono), homogeneousComponent_of_mem hmono]
    by_cases h : n = d.degree
    · simp [h]
    · simp [h]
  | add q r hq hr => simp only [mul_add, map_add, hq, hr]

/-- A nonzero homogeneous factor can be cancelled in a homogeneous-degree assertion. -/
theorem isHomogeneous_quotient_add {σ : Type*} {R : Type*}
    [CommRing R] [IsDomain R] {p q : MvPolynomial σ R} {m n : ℕ}
    (hp : p.IsHomogeneous m) (hp0 : p ≠ 0) (hpq : (p*q).IsHomogeneous (m+n)) :
    q.IsHomogeneous n := by
  have h := homogeneousComponent_mul_homogeneous hp q n
  rw [homogeneousComponent_eq_self hpq] at h
  have he := mul_left_cancel₀ hp0 h
  rw [he]
  exact homogeneousComponent_isHomogeneous n q

/-- Homogeneous division lowers the degree, with zero quotients allowed. -/
theorem isHomogeneous_quotient {σ : Type*} {R : Type*}
    [CommRing R] [IsDomain R] {p q : MvPolynomial σ R} {m n : ℕ}
    (hp : p.IsHomogeneous m) (hp0 : p ≠ 0) (hpq : (p*q).IsHomogeneous n) :
    q.IsHomogeneous (n-m) := by
  by_cases hq : q = 0
  · rw [hq]; exact isHomogeneous_zero σ R _
  have hmn : m ≤ n := by
    have he := hpq.totalDegree (mul_ne_zero hp0 hq)
    rw [totalDegree_mul_of_isDomain hp0 hq, hp.totalDegree hp0] at he
    omega
  apply isHomogeneous_quotient_add hp hp0
  simpa only [Nat.add_sub_of_le hmn] using hpq

end TernaryPoly
