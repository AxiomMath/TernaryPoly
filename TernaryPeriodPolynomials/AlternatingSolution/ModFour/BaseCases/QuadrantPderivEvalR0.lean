module

public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.QuadrantDecomposition

@[expose] public section



/-!
`evalR0` and `pderiv 0`/`pderiv 1` applied to a quadrant-decomposed `p : Poly2`, in terms of
`evalR2` of the four quadrant pieces. Needed to assemble the per-`j` symmetric witness for
`modFour_beta_triangular`'s first conjunct from the four `baseSym j m`-quadrant contributions.
-/

open MvPolynomial TernaryPoly.CharTwoNorm

namespace TernaryPeriodPolynomials.Argument.ModFourBeta

private theorem ne01 : (0 : Fin 3) ≠ 1 := by decide
private theorem ne10 : (1 : Fin 3) ≠ 0 := by decide

theorem evalR0_X0 : evalR0 (X 0) = d4 := by show bind₁ ![d4, d6, d7 ^ 2] (X 0) = d4; simp
theorem evalR0_X1 : evalR0 (X 1) = d6 := by show bind₁ ![d4, d6, d7 ^ 2] (X 1) = d6; simp

/-- `pderiv 1` of a quadrant-decomposed sum. -/
theorem pderiv1_quadrant_eq (A B D E : Poly2) :
    pderiv 1 (double A + X 1 * double B + X 0 * double D + X 0 * X 1 * double E)
      = double B + X 0 * double E := by
  have h1 : pderiv 1 (double A) = 0 := pderiv1_double A
  have h2 : pderiv 1 (double B) = 0 := pderiv1_double B
  have h3 : pderiv 1 (double D) = 0 := pderiv1_double D
  have h4 : pderiv 1 (double E) = 0 := pderiv1_double E
  have hX1 : pderiv 1 (X 1 : Poly2) = 1 := MvPolynomial.pderiv_X_self 1
  have hX0 : pderiv 1 (X 0 : Poly2) = 0 := MvPolynomial.pderiv_X_of_ne ne01
  simp only [map_add, MvPolynomial.pderiv_mul, h1, h2, h3, h4, hX1, hX0,
    mul_zero, zero_mul, add_zero, zero_add, mul_one, one_mul]

/-- `pderiv 0` of a quadrant-decomposed sum. -/
theorem pderiv0_quadrant_eq (A B D E : Poly2) :
    pderiv 0 (double A + X 1 * double B + X 0 * double D + X 0 * X 1 * double E)
      = double D + X 1 * double E := by
  have h1 : pderiv 0 (double A) = 0 := pderiv0_double A
  have h2 : pderiv 0 (double B) = 0 := pderiv0_double B
  have h3 : pderiv 0 (double D) = 0 := pderiv0_double D
  have h4 : pderiv 0 (double E) = 0 := pderiv0_double E
  have hX0 : pderiv 0 (X 0 : Poly2) = 1 := MvPolynomial.pderiv_X_self 0
  have hX1 : pderiv 0 (X 1 : Poly2) = 0 := MvPolynomial.pderiv_X_of_ne ne10
  simp only [map_add, MvPolynomial.pderiv_mul, h1, h2, h3, h4, hX0, hX1,
    mul_zero, zero_mul, add_zero, zero_add, one_mul]

/-- `evalR0` of a quadrant-decomposed `p`, in terms of `evalR2` of its four pieces. -/
theorem evalR0_quadrant_eq {p A B D E : Poly2}
    (hp : p = double A + X 1 * double B + X 0 * double D + X 0 * X 1 * double E) :
    evalR0 p = evalR2 A + d6 * evalR2 B + d4 * evalR2 D + d4 * d6 * evalR2 E := by
  rw [hp]
  simp only [map_add, map_mul, evalR0_double, evalR0_X0, evalR0_X1]

/-- `evalR0 (pderiv 1 p)` for a quadrant-decomposed `p`. -/
theorem evalR0_pderiv1_quadrant_eq {p A B D E : Poly2}
    (hp : p = double A + X 1 * double B + X 0 * double D + X 0 * X 1 * double E) :
    evalR0 (pderiv 1 p) = evalR2 B + d4 * evalR2 E := by
  rw [hp, pderiv1_quadrant_eq]
  simp only [map_add, map_mul, evalR0_double, evalR0_X0]

/-- `evalR0 (pderiv 0 p)` for a quadrant-decomposed `p`. -/
theorem evalR0_pderiv0_quadrant_eq {p A B D E : Poly2}
    (hp : p = double A + X 1 * double B + X 0 * double D + X 0 * X 1 * double E) :
    evalR0 (pderiv 0 p) = evalR2 D + d6 * evalR2 E := by
  rw [hp, pderiv0_quadrant_eq]
  simp only [map_add, map_mul, evalR0_double, evalR0_X1]

end TernaryPeriodPolynomials.Argument.ModFourBeta
