module

public import TernaryPeriodPolynomials.Polynomial.Translation
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence

@[expose] public section


open MvPolynomial

namespace TernaryPoly

private theorem finSuccEquiv_X_one :
    finSuccEquiv ℚ 1 (X (1 : Fin 2)) = Polynomial.C (X (0 : Fin 1)) :=
  finSuccEquiv_X_succ (R := ℚ) (n := 1) (j := 0)

private theorem finSuccEquiv_shear (g : MvPolynomial (Fin 2) ℚ) :
    finSuccEquiv ℚ 1 (bind₁ ![X 0 + X 1, X 1] g) =
      (finSuccEquiv ℚ 1 g).comp (Polynomial.X + Polynomial.C (X (0 : Fin 1))) := by
  induction g using MvPolynomial.induction_on with
  | C r => simp [finSuccEquiv_apply]
  | add p q hp hq => simp only [map_add, Polynomial.add_comp, hp, hq]
  | mul_X p i hp =>
    fin_cases i <;>
      simp [map_mul, hp, Polynomial.mul_comp, finSuccEquiv_X_zero,
        finSuccEquiv_X_one]

/-- A binary polynomial invariant under the first elementary shear omits its first variable. -/
theorem shear_invariant_first_variable (g : MvPolynomial (Fin 2) ℚ)
    (hg : bind₁ ![X 0 + X 1, X 1] g = g) :
    bind₁ ![0, X 1] g = g := by
  have ht : (finSuccEquiv ℚ 1 g).comp
      (Polynomial.X + Polynomial.C (X (0 : Fin 1))) = finSuccEquiv ℚ 1 g := by
    rw [← finSuccEquiv_shear, hg]
  have hc := polynomial_eq_constant_of_translation (finSuccEquiv ℚ 1 g)
    (X (0 : Fin 1)) (X_ne_zero 0) ht
  have hzero (g : MvPolynomial (Fin 2) ℚ) :
      finSuccEquiv ℚ 1 (bind₁ ![0, X 1] g) =
        Polynomial.C ((finSuccEquiv ℚ 1 g).coeff 0) := by
    induction g using MvPolynomial.induction_on with
    | C r => simp [finSuccEquiv_apply]
    | add p q hp hq => simp only [map_add, hp, hq, Polynomial.coeff_add]
    | mul_X p i hp =>
      fin_cases i <;>
        simp [map_mul, hp, finSuccEquiv_X_zero,
          finSuccEquiv_X_one]
  apply (finSuccEquiv ℚ 1).injective
  rw [hzero, hc]
  simp

end TernaryPoly
