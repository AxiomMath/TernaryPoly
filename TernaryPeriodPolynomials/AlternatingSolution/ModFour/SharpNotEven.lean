module

public import TernaryPeriodPolynomials.Polynomial.Defs
public import Mathlib.Algebra.Polynomial.Monic

@[expose] public section


/-! Non-divisibility-by-2 property of the sharpness example for Theorem 5.2 (`mf:thm:main`). -/

open MvPolynomial

namespace TernaryPeriodPolynomials.Argument

/-- `f = (x+y+z)²(x-y)(x-z)(y-z)` is not of the form `2g`. -/
theorem sharp_not_even :
    ¬ ∃ g : MvPolynomial (Fin 3) ℤ,
      ((X 0 + X 1 + X 2) ^ 2 * ((X 0 - X 1) * (X 0 - X 2) * (X 1 - X 2)) :
        MvPolynomial (Fin 3) ℤ) = C 2 * g := by
  rintro ⟨g, hg⟩
  have happ := congrArg (MvPolynomial.aeval (R := ℤ)
    (![Polynomial.X, 1, 0] : Fin 3 → Polynomial ℤ)) hg
  simp only [map_mul, map_add, map_sub, map_pow, MvPolynomial.aeval_X, MvPolynomial.aeval_C,
    Polynomial.algebraMap_eq, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons] at happ
  set h : Polynomial ℤ :=
    MvPolynomial.aeval (R := ℤ) (![Polynomial.X, 1, 0] : Fin 3 → Polynomial ℤ) g with hh_def
  have key : (Polynomial.X : Polynomial ℤ) * (Polynomial.X - 1) * (Polynomial.X + 1) ^ 2
      = Polynomial.C 2 * h := by
    rw [← happ]; ring
  have hmX : (Polynomial.X : Polynomial ℤ).Monic := Polynomial.monic_X
  have hmXm1 : (Polynomial.X - 1 : Polynomial ℤ).Monic := by
    simpa using Polynomial.monic_X_sub_C (1 : ℤ)
  have hmXp1 : (Polynomial.X + 1 : Polynomial ℤ).Monic := by
    simpa using Polynomial.monic_X_add_C (1 : ℤ)
  have hdX : (Polynomial.X : Polynomial ℤ).natDegree = 1 := Polynomial.natDegree_X
  have hdXm1 : (Polynomial.X - 1 : Polynomial ℤ).natDegree = 1 := by
    simpa using Polynomial.natDegree_X_sub_C (1 : ℤ)
  have hdXp1 : (Polynomial.X + 1 : Polynomial ℤ).natDegree = 1 := by
    simp
  have hmXp1sq : ((Polynomial.X + 1 : Polynomial ℤ) ^ 2).Monic := hmXp1.pow 2
  have hmProd :
      ((Polynomial.X : Polynomial ℤ) * (Polynomial.X - 1) * (Polynomial.X + 1) ^ 2).Monic :=
    (hmX.mul hmXm1).mul hmXp1sq
  have hdeg :
      ((Polynomial.X : Polynomial ℤ) * (Polynomial.X - 1) * (Polynomial.X + 1) ^ 2).natDegree
        = 4 := by
    rw [(hmX.mul hmXm1).natDegree_mul hmXp1sq, hmX.natDegree_mul hmXm1,
      Polynomial.Monic.natDegree_pow hmXp1 2, hdX, hdXm1, hdXp1]
  have hcoeff1 :
      ((Polynomial.X : Polynomial ℤ) * (Polynomial.X - 1) * (Polynomial.X + 1) ^ 2).coeff 4
        = 1 := by
    rw [← hdeg]; exact hmProd.coeff_natDegree
  rw [key, Polynomial.coeff_C_mul] at hcoeff1
  omega

end TernaryPeriodPolynomials.Argument
