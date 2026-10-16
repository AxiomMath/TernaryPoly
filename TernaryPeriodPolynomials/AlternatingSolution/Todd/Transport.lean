module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Rat.Defs
public import Mathlib.Tactic.FinCases
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.GroupWithZero.Indicator
public import Mathlib.Algebra.Module.Torsion.Field
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Polynomial.Eval.SMul
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
public import Mathlib.Tactic.Field

@[expose] public section


open MvPolynomial

noncomputable section

namespace TernaryPoly

/-- The original second coordinate becomes the first coefficient variable. -/
theorem finSuccEquiv_ternary_X_one :
    finSuccEquiv ℚ 2 (X (1 : Fin 3)) = Polynomial.C (X (0 : Fin 2)) :=
  finSuccEquiv_X_succ (R := ℚ) (n := 2) (j := 0)

/-- The original third coordinate becomes the second coefficient variable. -/
theorem finSuccEquiv_ternary_X_two :
    finSuccEquiv ℚ 2 (X (2 : Fin 3)) = Polynomial.C (X (1 : Fin 2)) :=
  finSuccEquiv_X_succ (R := ℚ) (n := 2) (j := 1)

/-- Taking the first partial derivative becomes univariate differentiation. -/
theorem finSuccEquiv_pderiv_zero (f : MvPolynomial (Fin 3) ℚ) :
    finSuccEquiv ℚ 2 (pderiv 0 f) = Polynomial.derivative (finSuccEquiv ℚ 2 f) := by
  induction f using MvPolynomial.induction_on with
  | C r => simp [finSuccEquiv_apply]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    fin_cases i <;>
      simp [map_mul, map_add, hp, Polynomial.derivative_mul,
        finSuccEquiv_X_zero, finSuccEquiv_ternary_X_one, finSuccEquiv_ternary_X_two,
        mul_comm]

/-- Translation by the original second coordinate is Taylor translation by `-Y`. -/
theorem finSuccEquiv_shift_Y (f : MvPolynomial (Fin 3) ℚ) :
    finSuccEquiv ℚ 2 (bind₁ ![X 0-X 1, X 1, X 2] f) =
      Polynomial.taylor (-X (0 : Fin 2)) (finSuccEquiv ℚ 2 f) := by
  induction f using MvPolynomial.induction_on with
  | C r => simp [finSuccEquiv_apply]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, Polynomial.taylor_mul, hp]
    fin_cases i <;>
      simp [finSuccEquiv_X_zero, finSuccEquiv_ternary_X_one,
        finSuccEquiv_ternary_X_two, sub_eq_add_neg]

/-- Translation by the original third coordinate is Taylor translation by `-Z`. -/
theorem finSuccEquiv_shift_Z (f : MvPolynomial (Fin 3) ℚ) :
    finSuccEquiv ℚ 2 (bind₁ ![X 0-X 2, X 1, X 2] f) =
      Polynomial.taylor (-X (1 : Fin 2)) (finSuccEquiv ℚ 2 f) := by
  induction f using MvPolynomial.induction_on with
  | C r => simp [finSuccEquiv_apply]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, Polynomial.taylor_mul, hp]
    fin_cases i <;>
      simp [finSuccEquiv_X_zero, finSuccEquiv_ternary_X_one,
        finSuccEquiv_ternary_X_two, sub_eq_add_neg]

/-- Multiplication by `Y` becomes multiplication by a coefficient constant. -/
theorem finSuccEquiv_Y_mul (f : MvPolynomial (Fin 3) ℚ) :
    finSuccEquiv ℚ 2 (X 1 * f) =
      Polynomial.C (X (0 : Fin 2)) * finSuccEquiv ℚ 2 f := by
  rw [map_mul, finSuccEquiv_ternary_X_one]

/-- Multiplication by `Z` becomes multiplication by a coefficient constant. -/
theorem finSuccEquiv_Z_mul (f : MvPolynomial (Fin 3) ℚ) :
    finSuccEquiv ℚ 2 (X 2 * f) =
      Polynomial.C (X (1 : Fin 2)) * finSuccEquiv ℚ 2 f := by
  rw [map_mul, finSuccEquiv_ternary_X_two]

end TernaryPoly
