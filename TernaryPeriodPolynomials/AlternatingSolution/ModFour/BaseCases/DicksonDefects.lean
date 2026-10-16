module

public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.LeibnizStep
public import TernaryPeriodPolynomials.Tactic.PolynomialLiteral

@[expose] public section



/-!
# Integral Leibniz defects of `liftD4` and `liftD6`

Explicit integral polynomials `E₁, E₂` witnessing `Aᵢ(liftD4) = liftD4 + 2 Eᵢ` and
`Aᵢ(liftD6) = liftD6 + 2 Eᵢ`, obtained by direct computer-algebra expansion and
checked here by `ring`.
-/

open MvPolynomial

namespace TernaryPeriodPolynomials.Argument.ModFourBeta

noncomputable def E1_D4 : MvPolynomial (Fin 3) ℤ :=
  poly_literal% (MvPolynomial (Fin 3) ℤ)
    (-6 * X 0 ^ 3 * X 1 + 9 * X 0 ^ 2 * X 1 ^ 2 - 21 * X 0 ^ 2 * X 1 * X 2 - 19 * X 0 * X 1 ^ 3 +
    21 * X 0 * X 1 ^ 2 * X 2 - 22 * X 0 * X 1 * X 2 ^ 2 + 8 * X 1 ^ 4 - 21 * X 1 ^ 3 * X 2 +
    11 * X 1 ^ 2 * X 2 ^ 2 - 6 * X 1 * X 2 ^ 3)

noncomputable def E2_D4 : MvPolynomial (Fin 3) ℤ :=
  poly_literal% (MvPolynomial (Fin 3) ℤ)
    (8 * X 0 ^ 4 - 19 * X 0 ^ 3 * X 1 - 21 * X 0 ^ 3 * X 2 + 9 * X 0 ^ 2 * X 1 ^ 2 +
    21 * X 0 ^ 2 * X 1 * X 2 + 11 * X 0 ^ 2 * X 2 ^ 2 - 6 * X 0 * X 1 ^ 3 -
    21 * X 0 * X 1 ^ 2 * X 2 - 22 * X 0 * X 1 * X 2 ^ 2 - 6 * X 0 * X 2 ^ 3)

noncomputable def E1_D6 : MvPolynomial (Fin 3) ℤ :=
  poly_literal% (MvPolynomial (Fin 3) ℤ)
    (-3 * X 0 ^ 4 * X 1 * X 2 - 4 * X 0 ^ 3 * X 1 ^ 3 + 6 * X 0 ^ 3 * X 1 ^ 2 * X 2 -
    14 * X 0 ^ 3 * X 1 * X 2 ^ 2 + 6 * X 0 ^ 2 * X 1 ^ 4 - 39 * X 0 ^ 2 * X 1 ^ 3 * X 2 +
    21 * X 0 ^ 2 * X 1 ^ 2 * X 2 ^ 2 - 15 * X 0 ^ 2 * X 1 * X 2 ^ 3 - 6 * X 0 * X 1 ^ 5 +
    36 * X 0 * X 1 ^ 4 * X 2 - 57 * X 0 * X 1 ^ 3 * X 2 ^ 2 + 15 * X 0 * X 1 ^ 2 * X 2 ^ 3 -
    4 * X 0 * X 1 * X 2 ^ 4 + 2 * X 1 ^ 6 - 15 * X 1 ^ 5 * X 2 + 25 * X 1 ^ 4 * X 2 ^ 2 -
    15 * X 1 ^ 3 * X 2 ^ 3 + 2 * X 1 ^ 2 * X 2 ^ 4)

noncomputable def E2_D6 : MvPolynomial (Fin 3) ℤ :=
  poly_literal% (MvPolynomial (Fin 3) ℤ)
    (2 * X 0 ^ 6 - 6 * X 0 ^ 5 * X 1 - 15 * X 0 ^ 5 * X 2 + 6 * X 0 ^ 4 * X 1 ^ 2 +
    36 * X 0 ^ 4 * X 1 * X 2 + 25 * X 0 ^ 4 * X 2 ^ 2 - 4 * X 0 ^ 3 * X 1 ^ 3 -
    39 * X 0 ^ 3 * X 1 ^ 2 * X 2 - 57 * X 0 ^ 3 * X 1 * X 2 ^ 2 - 15 * X 0 ^ 3 * X 2 ^ 3 +
    6 * X 0 ^ 2 * X 1 ^ 3 * X 2 + 21 * X 0 ^ 2 * X 1 ^ 2 * X 2 ^ 2 + 15 * X 0 ^ 2 * X 1 * X 2 ^ 3 +
    2 * X 0 ^ 2 * X 2 ^ 4 - 3 * X 0 * X 1 ^ 4 * X 2 - 14 * X 0 * X 1 ^ 3 * X 2 ^ 2 -
    15 * X 0 * X 1 ^ 2 * X 2 ^ 3 - 4 * X 0 * X 1 * X 2 ^ 4)

theorem h1_D4 : bind₁ A1vec liftD4 = liftD4 + C 2 * E1_D4 := by
  simp only [liftD4, liftA, liftB, liftC, A1vec, E1_D4, map_add, map_mul, map_pow, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, map_ofNat]
  ring

theorem h2_D4 : bind₁ A2vec liftD4 = liftD4 + C 2 * E2_D4 := by
  simp only [liftD4, liftA, liftB, liftC, A2vec, E2_D4, map_add, map_mul, map_pow, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, map_ofNat]
  ring

theorem h1_D6 : bind₁ A1vec liftD6 = liftD6 + C 2 * E1_D6 := by
  simp only [liftD6, liftA, liftB, liftC, A1vec, E1_D6, map_add, map_mul, map_pow, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, map_ofNat]
  ring

theorem h2_D6 : bind₁ A2vec liftD6 = liftD6 + C 2 * E2_D6 := by
  simp only [liftD6, liftA, liftB, liftC, A2vec, E2_D6, map_add, map_mul, map_pow, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, map_ofNat]
  ring

end TernaryPeriodPolynomials.Argument.ModFourBeta
