module

public import Mathlib.Algebra.MvPolynomial.Coeff
public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum
public import Mathlib.Algebra.BigOperators.Associated
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.GroupWithZero.Indicator
public import Mathlib.Algebra.Module.Torsion.Field
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


/-! # Additive polynomial rigidity over rational coefficient algebras

Doubling alone forces a polynomial to have degree one in the doubled variable.
This coefficient argument also works when the coefficient algebra has nilpotents.
-/


noncomputable section
open MvPolynomial

namespace TernaryPoly.Paper

variable {R : Type*} [CommRing R]

/-- Scaling the first variable multiplies each coefficient by the corresponding power. -/
theorem coeff_scale_first (q : MvPolynomial (Fin 2) R) (a : R)
    (d : Fin 2 →₀ ℕ) :
    (bind₁ ![C a * X 0, X 1] q).coeff d = a ^ d 0 * q.coeff d := by
  classical
  induction q using MvPolynomial.induction_on' with
  | add p q hp hq => simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hp, hq, mul_add]
  | monomial e c =>
    have he : bind₁ (![C a * X 0, X 1] : Fin 2 → MvPolynomial (Fin 2) R)
        (monomial e c) = C (a ^ e 0) * monomial e c := by
      rw [monomial_fin_two]
      simp only [map_mul, map_pow, bind₁_C_right, bind₁_X_right, Matrix.cons_val_zero,
        Matrix.cons_val_one, mul_pow]
      rw [← map_pow]
      ring
    rw [he, coeff_C_mul]
    by_cases h : e = d
    · subst e; rfl
    · simp [coeff_monomial, h]

/-- A rational doubling relation kills every coefficient whose first exponent is not one. -/
theorem coeff_eq_zero_of_doubling [Algebra ℚ R] (q : MvPolynomial (Fin 2) R)
    (hq : bind₁ ![2 * X 0, X 1] q = 2 * q)
    (d : Fin 2 →₀ ℕ) (hd : d 0 ≠ 1) : q.coeff d = 0 := by
  have h := congrArg (·.coeff d) hq
  have hc : C (2 : R) = (2 : MvPolynomial (Fin 2) R) := map_ofNat C 2
  rw [← hc, coeff_scale_first, coeff_C_mul] at h
  have hmul : ((2 : R) ^ d 0 - 2) * q.coeff d = 0 := by
    rw [sub_mul, h, sub_self]
  have hrat : (2 : ℚ) ^ d 0 - 2 ≠ 0 := by
    rw [sub_ne_zero]
    intro heq
    have hh : (2 : ℚ) ^ d 0 = 2 ^ (1 : ℕ) := by simpa using heq
    exact hd ((pow_right_injective₀ (by norm_num : (0 : ℚ) < 2)
      (by norm_num : (2 : ℚ) ≠ 1)) hh)
  have hu : IsUnit ((2 : R) ^ d 0 - 2) := by
    simpa only [map_sub, map_pow, map_ofNat] using
      (isUnit_iff_ne_zero.mpr hrat).map (algebraMap ℚ R)
  exact (hu.mul_right_eq_zero).mp hmul

/-- Literal reconstruction of a polynomial satisfying the doubling identity. -/
theorem eq_X_mul_axis_of_doubling [Algebra ℚ R] (q : MvPolynomial (Fin 2) R)
    (hq : bind₁ ![2 * X 0, X 1] q = 2 * q) :
    q = X 0 * bind₁ ![1, X 1] q := by
  classical
  calc
    q = ∑ d ∈ q.support, monomial d (q.coeff d) := q.as_sum
    _ = ∑ d ∈ q.support, X 0 * bind₁ ![1, X 1] (monomial d (q.coeff d)) := by
      apply Finset.sum_congr rfl
      intro d hd
      have hd0 : d 0 = 1 := by
        by_contra h
        exact (mem_support_iff.mp hd) (coeff_eq_zero_of_doubling q hq d h)
      rw [monomial_fin_two, hd0]
      simp only [map_mul, map_pow, bind₁_C_right, bind₁_X_right,
        Matrix.cons_val_zero, Matrix.cons_val_one, pow_one]
      ring
    _ = X 0 * bind₁ ![1, X 1] q := by
      rw [← Finset.mul_sum, ← map_sum, support_sum_monomial_coeff]

end TernaryPoly.Paper
