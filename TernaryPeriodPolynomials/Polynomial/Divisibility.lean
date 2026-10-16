module

public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Tactic.Ring
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.GroupWithZero.Indicator
public import Mathlib.Algebra.Module.Torsion.Field
public import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.Data.List.Enum
public import Mathlib.Data.String.Defs
public import Mathlib.Lean.Elab.InfoTree
public import Mathlib.Lean.Elab.Tactic.Basic
public import Mathlib.Lean.Elab.Tactic.Meta
public import Mathlib.Lean.Expr.Basic
public import Mathlib.Lean.Expr.ExtraRecognizers
public import Mathlib.Lean.Expr.Rat
public import Mathlib.Lean.GoalsLocation
public import Mathlib.Lean.MessageData.Trace
public import Mathlib.Lean.Meta
public import Mathlib.Lean.Meta.Basic
public import Mathlib.Lean.Meta.KAbstractPositions
public import Mathlib.Lean.PrettyPrinter.Delaborator
public import Mathlib.Tactic.Basify.Attr

@[expose] public section


open MvPolynomial

namespace TernaryPoly

/-- Changing one variable changes a polynomial by a multiple of that variable difference. -/
theorem variable_substitution_dvd {σ R : Type*} [CommRing R] [DecidableEq σ]
    (f : MvPolynomial σ R) (i : σ) (p : MvPolynomial σ R) :
    X i - p ∣ f - bind₁ (Function.update X i p) f := by
  induction f using MvPolynomial.induction_on with
  | C r => simp
  | add f g hf hg =>
    rw [map_add, add_sub_add_comm]
    exact dvd_add hf hg
  | mul_X f j hf =>
    have hj : X i - p ∣ X j - Function.update X i p j := by
      by_cases hij : j = i
      · subst j
        simp
      · simp [Function.update_of_ne hij]
    have h := dvd_add (dvd_mul_of_dvd_left hf (X j))
      (dvd_mul_of_dvd_right hj (bind₁ (Function.update X i p) f))
    rw [map_mul, bind₁_X_right]
    convert h using 1; ring

/-- A zero specialization provides the corresponding linear factor. -/
theorem linear_factor_dvd_of_substitution_zero {σ R : Type*} [CommRing R] [DecidableEq σ]
    (f : MvPolynomial σ R) (i : σ) (p : MvPolynomial σ R)
    (hf : bind₁ (Function.update X i p) f = 0) : X i - p ∣ f := by
  simpa only [hf, sub_zero] using variable_substitution_dvd f i p

/-- A new linear factor can be appended when the old divisor survives the specialization. -/
theorem mul_linear_factor_dvd_of_substitution_zero {σ R : Type*}
    [CommRing R] [IsDomain R] [DecidableEq σ]
    (f d : MvPolynomial σ R) (i : σ) (p : MvPolynomial σ R)
    (hd : d ∣ f) (hf : bind₁ (Function.update X i p) f = 0)
    (hkeep : bind₁ (Function.update X i p) d ≠ 0) : (d * (X i - p)) ∣ f := by
  obtain ⟨q, rfl⟩ := hd
  have hq : bind₁ (Function.update X i p) q = 0 := by
    rw [map_mul] at hf
    exact (mul_eq_zero.mp hf).resolve_left hkeep
  obtain ⟨r, hr⟩ := linear_factor_dvd_of_substitution_zero q i p hq
  exact ⟨r, by rw [hr, mul_assoc]⟩

end TernaryPoly
