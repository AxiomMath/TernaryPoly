module

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.GroupWithZero.Indicator
public import Mathlib.Algebra.Module.Submodule.EqLocus
public import Mathlib.Algebra.Module.Torsion.Field
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Polynomial.Degree.Domain
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
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.Tactic.Basify.Attr

@[expose] public section

/-! # The axis-normalized antiderivative of a polynomial over a rational algebra -/

open Polynomial

noncomputable section

namespace TernaryPoly

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- The unique linear antiderivative with zero constant coefficient. -/
def polyIntegral : Polynomial R →ₗ[R] Polynomial R :=
  Polynomial.lsum fun n =>
    algebraMap ℚ R (((n : ℚ) + 1)⁻¹) • (Polynomial.monomial (n + 1))

/-- Integration divides the coefficient by the new exponent. -/
@[simp] theorem polyIntegral_monomial (n : ℕ) (r : R) :
    polyIntegral (monomial n r) =
      monomial (n + 1) (algebraMap ℚ R (((n : ℚ) + 1)⁻¹) * r) := by
  simp [polyIntegral, Polynomial.lsum_apply, Polynomial.sum_monomial_index,
    smul_monomial, smul_eq_mul]

private theorem integral_denominator_cancel (n : ℕ) :
    algebraMap ℚ R (((n : ℚ) + 1)⁻¹) * ((n : R) + 1) = 1 := by
  have h := congrArg (algebraMap ℚ R) (inv_mul_cancel₀ (Nat.cast_add_one_ne_zero (R := ℚ) n))
  simpa only [map_mul, map_add, map_natCast, map_one] using h

/-- Differentiating the normalized antiderivative recovers the input polynomial. -/
@[simp] theorem derivative_polyIntegral (p : Polynomial R) :
    derivative (polyIntegral p) = p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq]
  | monomial n r =>
      rw [polyIntegral_monomial, derivative_monomial_succ]
      congr 1
      calc
        (algebraMap ℚ R (((n : ℚ) + 1)⁻¹) * r) * ((n : R) + 1) =
            (algebraMap ℚ R (((n : ℚ) + 1)⁻¹) * ((n : R) + 1)) * r := by ac_rfl
        _ = r := by rw [integral_denominator_cancel, one_mul]

/-- The normalization fixes the constant of integration to zero. -/
@[simp] theorem polyIntegral_coeff_zero (p : Polynomial R) :
    (polyIntegral p).coeff 0 = 0 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, coeff_add, hp, hq, add_zero]
  | monomial n r => simp [polyIntegral_monomial]

/-- Derivative and constant coefficient determine a polynomial over a rational algebra. -/
theorem polynomial_eq_of_derivative_eq_of_coeff_zero_eq (p q : Polynomial R)
    (hd : derivative p = derivative q) (h0 : p.coeff 0 = q.coeff 0) : p = q := by
  ext n
  cases n with
  | zero => exact h0
  | succ n =>
      have h := congrArg (fun f : Polynomial R => f.coeff n) hd
      rw [coeff_derivative, coeff_derivative] at h
      have hc : ((n : R) + 1) * algebraMap ℚ R (((n : ℚ) + 1)⁻¹) = 1 := by
        rw [mul_comm, integral_denominator_cancel]
      have h' := congrArg (fun r : R => r * algebraMap ℚ R (((n : ℚ) + 1)⁻¹)) h
      simpa only [mul_assoc, hc, mul_one] using h'

/-- The derivative and the zero constant coefficient characterize the normalized integral. -/
theorem polyIntegral_unique (p q : Polynomial R) (hd : derivative q = p)
    (h0 : q.coeff 0 = 0) : q = polyIntegral p := by
  apply polynomial_eq_of_derivative_eq_of_coeff_zero_eq
  · rw [derivative_polyIntegral, hd]
  · rw [polyIntegral_coeff_zero, h0]

/-- Every polynomial over a rational algebra has a polynomial antiderivative. -/
theorem polynomial_derivative_surjective : Function.Surjective (derivative (R := R)) :=
  fun p => ⟨polyIntegral p, derivative_polyIntegral p⟩

end TernaryPoly
