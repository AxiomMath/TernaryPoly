module

public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.Defs
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.ExplicitLiftConstruction
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.QuadrantDecomposition
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Base.Cases
public import TernaryPeriodPolynomials.Tactic.PolynomialLiteral

@[expose] public section


/-! More base cases for the 32-case `W(j,m)` table (continuation of `BaseCases.lean`).
-/

open MvPolynomial
open TernaryPoly.CharTwoNorm (a b c cplus d7 basis generator)

namespace TernaryPeriodPolynomials.Argument.ModFourBeta

theorem half_3_0 :
    threeTermNorm (baseSym 3 0) = C 2 *
      (poly_literal% (@MvPolynomial (Fin 3) ℤ CommRing.toCommSemiring) (-4 * X 0 ^ 7 + 14 * X 0 ^ 6 * X 1 + 24 * X 0 ^ 6 * X 2 - 18 * X 0 ^ 5 * X 1 ^ 2 - 72 * X 0 ^ 5 * X 1 * X 2 - 48 * X 0 ^ 5 * X 2 ^ 2 + 10 * X 0 ^ 4 * X 1 ^ 3 + 99 * X 0 ^ 4 * X 1 ^ 2 * X 2 + 120 * X 0 ^ 4 * X 1 * X 2 ^ 2 + 44 * X 0 ^ 4 * X 2 ^ 3 + 10 * X 0 ^ 3 * X 1 ^ 4 - 78 * X 0 ^ 3 * X 1 ^ 3 * X 2 - 48 * X 0 ^ 3 * X 1 ^ 2 * X 2 ^ 2 - 88 * X 0 ^ 3 * X 1 * X 2 ^ 3 - 12 * X 0 ^ 3 * X 2 ^ 4 - 18 * X 0 ^ 2 * X 1 ^ 5 + 99 * X 0 ^ 2 * X 1 ^ 4 * X 2 - 48 * X 0 ^ 2 * X 1 ^ 3 * X 2 ^ 2 + 132 * X 0 ^ 2 * X 1 ^ 2 * X 2 ^ 3 + 18 * X 0 ^ 2 * X 1 * X 2 ^ 4 + 3 * X 0 ^ 2 * X 2 ^ 5 + 14 * X 0 * X 1 ^ 6 - 72 * X 0 * X 1 ^ 5 * X 2 + 120 * X 0 * X 1 ^ 4 * X 2 ^ 2 - 88 * X 0 * X 1 ^ 3 * X 2 ^ 3 + 18 * X 0 * X 1 ^ 2 * X 2 ^ 4 - 3 * X 0 * X 1 * X 2 ^ 5 - 4 * X 1 ^ 7 + 24 * X 1 ^ 6 * X 2 - 48 * X 1 ^ 5 * X 2 ^ 2 + 44 * X 1 ^ 4 * X 2 ^ 3 - 12 * X 1 ^ 3 * X 2 ^ 4 + 3 * X 1 ^ 2 * X 2 ^ 5)) := by
  simp [baseSym, mult, oddGenLiftSym, genLiftSym, basisLift, kappa, liftD7, liftCplus, liftC,
    liftB, liftA, liftD4, liftD6, threeTermNorm]
  ring

theorem reduceTwo_g30 :
    reduceTwo
      (poly_literal% (MvPolynomial (Fin 3) ℤ) (-4 * X 0 ^ 7 + 14 * X 0 ^ 6 * X 1 + 24 * X 0 ^ 6 * X 2 - 18 * X 0 ^ 5 * X 1 ^ 2 - 72 * X 0 ^ 5 * X 1 * X 2 - 48 * X 0 ^ 5 * X 2 ^ 2 + 10 * X 0 ^ 4 * X 1 ^ 3 + 99 * X 0 ^ 4 * X 1 ^ 2 * X 2 + 120 * X 0 ^ 4 * X 1 * X 2 ^ 2 + 44 * X 0 ^ 4 * X 2 ^ 3 + 10 * X 0 ^ 3 * X 1 ^ 4 - 78 * X 0 ^ 3 * X 1 ^ 3 * X 2 - 48 * X 0 ^ 3 * X 1 ^ 2 * X 2 ^ 2 - 88 * X 0 ^ 3 * X 1 * X 2 ^ 3 - 12 * X 0 ^ 3 * X 2 ^ 4 - 18 * X 0 ^ 2 * X 1 ^ 5 + 99 * X 0 ^ 2 * X 1 ^ 4 * X 2 - 48 * X 0 ^ 2 * X 1 ^ 3 * X 2 ^ 2 + 132 * X 0 ^ 2 * X 1 ^ 2 * X 2 ^ 3 + 18 * X 0 ^ 2 * X 1 * X 2 ^ 4 + 3 * X 0 ^ 2 * X 2 ^ 5 + 14 * X 0 * X 1 ^ 6 - 72 * X 0 * X 1 ^ 5 * X 2 + 120 * X 0 * X 1 ^ 4 * X 2 ^ 2 - 88 * X 0 * X 1 ^ 3 * X 2 ^ 3 + 18 * X 0 * X 1 ^ 2 * X 2 ^ 4 - 3 * X 0 * X 1 * X 2 ^ 5 - 4 * X 1 ^ 7 + 24 * X 1 ^ 6 * X 2 - 48 * X 1 ^ 5 * X 2 ^ 2 + 44 * X 1 ^ 4 * X 2 ^ 3 - 12 * X 1 ^ 3 * X 2 ^ 4 + 3 * X 1 ^ 2 * X 2 ^ 5)) =
      ((poly_literal% Poly2 (X 0 ^ 4 * X 1 ^ 2 * X 2 + X 0 ^ 2 * X 1 ^ 4 * X 2 + X 0 ^ 2 * X 2 ^ 5 + X 0 * X 1 * X 2 ^ 5 + X 1 ^ 2 * X 2 ^ 5)) : Poly2) := by
  simp [reduceTwo, CharTwo.sub_eq_add]; ring_nf; simp only [ofNat_mod_poly2]; ring

theorem pi_3_0 :
    piOperator
      ((poly_literal% Poly2 (X 0 ^ 4 * X 1 ^ 2 * X 2 + X 0 ^ 2 * X 1 ^ 4 * X 2 + X 0 ^ 2 * X 2 ^ 5 + X 0 * X 1 * X 2 ^ 5 + X 1 ^ 2 * X 2 ^ 5)) : Poly2) = 0 := by
  simp [piOperator, piSubstitutions]
  ring_nf
  simp [ofNat_mod_poly2]

/-- **Case (3,0), fully closed.** -/
theorem case_3_0 :
    threeTermNorm (baseSym 3 0) = C 2 *
      (poly_literal% (@MvPolynomial (Fin 3) ℤ CommRing.toCommSemiring) (-4 * X 0 ^ 7 + 14 * X 0 ^ 6 * X 1 + 24 * X 0 ^ 6 * X 2 - 18 * X 0 ^ 5 * X 1 ^ 2 - 72 * X 0 ^ 5 * X 1 * X 2 - 48 * X 0 ^ 5 * X 2 ^ 2 + 10 * X 0 ^ 4 * X 1 ^ 3 + 99 * X 0 ^ 4 * X 1 ^ 2 * X 2 + 120 * X 0 ^ 4 * X 1 * X 2 ^ 2 + 44 * X 0 ^ 4 * X 2 ^ 3 + 10 * X 0 ^ 3 * X 1 ^ 4 - 78 * X 0 ^ 3 * X 1 ^ 3 * X 2 - 48 * X 0 ^ 3 * X 1 ^ 2 * X 2 ^ 2 - 88 * X 0 ^ 3 * X 1 * X 2 ^ 3 - 12 * X 0 ^ 3 * X 2 ^ 4 - 18 * X 0 ^ 2 * X 1 ^ 5 + 99 * X 0 ^ 2 * X 1 ^ 4 * X 2 - 48 * X 0 ^ 2 * X 1 ^ 3 * X 2 ^ 2 + 132 * X 0 ^ 2 * X 1 ^ 2 * X 2 ^ 3 + 18 * X 0 ^ 2 * X 1 * X 2 ^ 4 + 3 * X 0 ^ 2 * X 2 ^ 5 + 14 * X 0 * X 1 ^ 6 - 72 * X 0 * X 1 ^ 5 * X 2 + 120 * X 0 * X 1 ^ 4 * X 2 ^ 2 - 88 * X 0 * X 1 ^ 3 * X 2 ^ 3 + 18 * X 0 * X 1 ^ 2 * X 2 ^ 4 - 3 * X 0 * X 1 * X 2 ^ 5 - 4 * X 1 ^ 7 + 24 * X 1 ^ 6 * X 2 - 48 * X 1 ^ 5 * X 2 ^ 2 + 44 * X 1 ^ 4 * X 2 ^ 3 - 12 * X 1 ^ 3 * X 2 ^ 4 + 3 * X 1 ^ 2 * X 2 ^ 5)) ∧
    piOperator
      (reduceTwo
        (poly_literal% (MvPolynomial (Fin 3) ℤ) (-4 * X 0 ^ 7 + 14 * X 0 ^ 6 * X 1 + 24 * X 0 ^ 6 * X 2 - 18 * X 0 ^ 5 * X 1 ^ 2 - 72 * X 0 ^ 5 * X 1 * X 2 - 48 * X 0 ^ 5 * X 2 ^ 2 + 10 * X 0 ^ 4 * X 1 ^ 3 + 99 * X 0 ^ 4 * X 1 ^ 2 * X 2 + 120 * X 0 ^ 4 * X 1 * X 2 ^ 2 + 44 * X 0 ^ 4 * X 2 ^ 3 + 10 * X 0 ^ 3 * X 1 ^ 4 - 78 * X 0 ^ 3 * X 1 ^ 3 * X 2 - 48 * X 0 ^ 3 * X 1 ^ 2 * X 2 ^ 2 - 88 * X 0 ^ 3 * X 1 * X 2 ^ 3 - 12 * X 0 ^ 3 * X 2 ^ 4 - 18 * X 0 ^ 2 * X 1 ^ 5 + 99 * X 0 ^ 2 * X 1 ^ 4 * X 2 - 48 * X 0 ^ 2 * X 1 ^ 3 * X 2 ^ 2 + 132 * X 0 ^ 2 * X 1 ^ 2 * X 2 ^ 3 + 18 * X 0 ^ 2 * X 1 * X 2 ^ 4 + 3 * X 0 ^ 2 * X 2 ^ 5 + 14 * X 0 * X 1 ^ 6 - 72 * X 0 * X 1 ^ 5 * X 2 + 120 * X 0 * X 1 ^ 4 * X 2 ^ 2 - 88 * X 0 * X 1 ^ 3 * X 2 ^ 3 + 18 * X 0 * X 1 ^ 2 * X 2 ^ 4 - 3 * X 0 * X 1 * X 2 ^ 5 - 4 * X 1 ^ 7 + 24 * X 1 ^ 6 * X 2 - 48 * X 1 ^ 5 * X 2 ^ 2 + 44 * X 1 ^ 4 * X 2 ^ 3 - 12 * X 1 ^ 3 * X 2 ^ 4 + 3 * X 1 ^ 2 * X 2 ^ 5))) = 0 :=
  ⟨half_3_0, by rw [reduceTwo_g30]; exact pi_3_0⟩

theorem half_1_2 :
    threeTermNorm (baseSym 1 2) = C 2 *
      (poly_literal% (@MvPolynomial (Fin 3) ℤ CommRing.toCommSemiring) (-68 * X 0 ^ 9 + 306 * X 0 ^ 8 * X 1 + 425 * X 0 ^ 8 * X 2 - 582 * X 0 ^ 7 * X 1 ^ 2 - 1700 * X 0 ^ 7 * X 1 * X 2 - 1006 * X 0 ^ 7 * X 2 ^ 2 + 609 * X 0 ^ 6 * X 1 ^ 3 + 3032 * X 0 ^ 6 * X 1 ^ 2 * X 2 + 3521 * X 0 ^ 6 * X 1 * X 2 ^ 2 + 1283 * X 0 ^ 6 * X 2 ^ 3 - 231 * X 0 ^ 5 * X 1 ^ 4 - 3146 * X 0 ^ 5 * X 1 ^ 3 * X 2 - 4527 * X 0 ^ 5 * X 1 ^ 2 * X 2 ^ 2 - 3849 * X 0 ^ 5 * X 1 * X 2 ^ 3 - 870 * X 0 ^ 5 * X 2 ^ 4 - 231 * X 0 ^ 4 * X 1 ^ 5 + 3203 * X 0 ^ 4 * X 1 ^ 4 * X 2 + 2515 * X 0 ^ 4 * X 1 ^ 3 * X 2 ^ 2 + 5841 * X 0 ^ 4 * X 1 ^ 2 * X 2 ^ 3 + 2175 * X 0 ^ 4 * X 1 * X 2 ^ 4 + 431 * X 0 ^ 4 * X 2 ^ 5 + 609 * X 0 ^ 3 * X 1 ^ 6 - 3146 * X 0 ^ 3 * X 1 ^ 5 * X 2 + 2515 * X 0 ^ 3 * X 1 ^ 4 * X 2 ^ 2 - 5267 * X 0 ^ 3 * X 1 ^ 3 * X 2 ^ 3 - 870 * X 0 ^ 3 * X 1 ^ 2 * X 2 ^ 4 - 862 * X 0 ^ 3 * X 1 * X 2 ^ 5 - 80 * X 0 ^ 3 * X 2 ^ 6 - 582 * X 0 ^ 2 * X 1 ^ 7 + 3032 * X 0 ^ 2 * X 1 ^ 6 * X 2 - 4527 * X 0 ^ 2 * X 1 ^ 5 * X 2 ^ 2 + 5841 * X 0 ^ 2 * X 1 ^ 4 * X 2 ^ 3 - 870 * X 0 ^ 2 * X 1 ^ 3 * X 2 ^ 4 + 1293 * X 0 ^ 2 * X 1 ^ 2 * X 2 ^ 5 + 120 * X 0 ^ 2 * X 1 * X 2 ^ 6 + 22 * X 0 ^ 2 * X 2 ^ 7 + 306 * X 0 * X 1 ^ 8 - 1700 * X 0 * X 1 ^ 7 * X 2 + 3521 * X 0 * X 1 ^ 6 * X 2 ^ 2 - 3849 * X 0 * X 1 ^ 5 * X 2 ^ 3 + 2175 * X 0 * X 1 ^ 4 * X 2 ^ 4 - 862 * X 0 * X 1 ^ 3 * X 2 ^ 5 + 120 * X 0 * X 1 ^ 2 * X 2 ^ 6 - 22 * X 0 * X 1 * X 2 ^ 7 - 68 * X 1 ^ 9 + 425 * X 1 ^ 8 * X 2 - 1006 * X 1 ^ 7 * X 2 ^ 2 + 1283 * X 1 ^ 6 * X 2 ^ 3 - 870 * X 1 ^ 5 * X 2 ^ 4 + 431 * X 1 ^ 4 * X 2 ^ 5 - 80 * X 1 ^ 3 * X 2 ^ 6 + 22 * X 1 ^ 2 * X 2 ^ 7)) := by
  simp [baseSym, mult, oddGenLiftSym, genLiftSym, basisLift, kappa, liftD7, liftCplus, liftC,
    liftB, liftA, liftD4, liftD6, threeTermNorm]
  ring

set_option maxRecDepth 4096 in
theorem reduceTwo_g12 :
    reduceTwo
      (poly_literal% (MvPolynomial (Fin 3) ℤ) (-68 * X 0 ^ 9 + 306 * X 0 ^ 8 * X 1 + 425 * X 0 ^ 8 * X 2 - 582 * X 0 ^ 7 * X 1 ^ 2 - 1700 * X 0 ^ 7 * X 1 * X 2 - 1006 * X 0 ^ 7 * X 2 ^ 2 + 609 * X 0 ^ 6 * X 1 ^ 3 + 3032 * X 0 ^ 6 * X 1 ^ 2 * X 2 + 3521 * X 0 ^ 6 * X 1 * X 2 ^ 2 + 1283 * X 0 ^ 6 * X 2 ^ 3 - 231 * X 0 ^ 5 * X 1 ^ 4 - 3146 * X 0 ^ 5 * X 1 ^ 3 * X 2 - 4527 * X 0 ^ 5 * X 1 ^ 2 * X 2 ^ 2 - 3849 * X 0 ^ 5 * X 1 * X 2 ^ 3 - 870 * X 0 ^ 5 * X 2 ^ 4 - 231 * X 0 ^ 4 * X 1 ^ 5 + 3203 * X 0 ^ 4 * X 1 ^ 4 * X 2 + 2515 * X 0 ^ 4 * X 1 ^ 3 * X 2 ^ 2 + 5841 * X 0 ^ 4 * X 1 ^ 2 * X 2 ^ 3 + 2175 * X 0 ^ 4 * X 1 * X 2 ^ 4 + 431 * X 0 ^ 4 * X 2 ^ 5 + 609 * X 0 ^ 3 * X 1 ^ 6 - 3146 * X 0 ^ 3 * X 1 ^ 5 * X 2 + 2515 * X 0 ^ 3 * X 1 ^ 4 * X 2 ^ 2 - 5267 * X 0 ^ 3 * X 1 ^ 3 * X 2 ^ 3 - 870 * X 0 ^ 3 * X 1 ^ 2 * X 2 ^ 4 - 862 * X 0 ^ 3 * X 1 * X 2 ^ 5 - 80 * X 0 ^ 3 * X 2 ^ 6 - 582 * X 0 ^ 2 * X 1 ^ 7 + 3032 * X 0 ^ 2 * X 1 ^ 6 * X 2 - 4527 * X 0 ^ 2 * X 1 ^ 5 * X 2 ^ 2 + 5841 * X 0 ^ 2 * X 1 ^ 4 * X 2 ^ 3 - 870 * X 0 ^ 2 * X 1 ^ 3 * X 2 ^ 4 + 1293 * X 0 ^ 2 * X 1 ^ 2 * X 2 ^ 5 + 120 * X 0 ^ 2 * X 1 * X 2 ^ 6 + 22 * X 0 ^ 2 * X 2 ^ 7 + 306 * X 0 * X 1 ^ 8 - 1700 * X 0 * X 1 ^ 7 * X 2 + 3521 * X 0 * X 1 ^ 6 * X 2 ^ 2 - 3849 * X 0 * X 1 ^ 5 * X 2 ^ 3 + 2175 * X 0 * X 1 ^ 4 * X 2 ^ 4 - 862 * X 0 * X 1 ^ 3 * X 2 ^ 5 + 120 * X 0 * X 1 ^ 2 * X 2 ^ 6 - 22 * X 0 * X 1 * X 2 ^ 7 - 68 * X 1 ^ 9 + 425 * X 1 ^ 8 * X 2 - 1006 * X 1 ^ 7 * X 2 ^ 2 + 1283 * X 1 ^ 6 * X 2 ^ 3 - 870 * X 1 ^ 5 * X 2 ^ 4 + 431 * X 1 ^ 4 * X 2 ^ 5 - 80 * X 1 ^ 3 * X 2 ^ 6 + 22 * X 1 ^ 2 * X 2 ^ 7)) =
      ((poly_literal% Poly2 (X 0 ^ 8 * X 2 + X 0 ^ 6 * X 1 ^ 3 + X 0 ^ 6 * X 1 * X 2 ^ 2 + X 0 ^ 6 * X 2 ^ 3 + X 0 ^ 5 * X 1 ^ 4 + X 0 ^ 5 * X 1 ^ 2 * X 2 ^ 2 + X 0 ^ 5 * X 1 * X 2 ^ 3 + X 0 ^ 4 * X 1 ^ 5 + X 0 ^ 4 * X 1 ^ 4 * X 2 + X 0 ^ 4 * X 1 ^ 3 * X 2 ^ 2 + X 0 ^ 4 * X 1 ^ 2 * X 2 ^ 3 + X 0 ^ 4 * X 1 * X 2 ^ 4 + X 0 ^ 4 * X 2 ^ 5 + X 0 ^ 3 * X 1 ^ 6 + X 0 ^ 3 * X 1 ^ 4 * X 2 ^ 2 + X 0 ^ 3 * X 1 ^ 3 * X 2 ^ 3 + X 0 ^ 2 * X 1 ^ 5 * X 2 ^ 2 + X 0 ^ 2 * X 1 ^ 4 * X 2 ^ 3 + X 0 ^ 2 * X 1 ^ 2 * X 2 ^ 5 + X 0 * X 1 ^ 6 * X 2 ^ 2 + X 0 * X 1 ^ 5 * X 2 ^ 3 + X 0 * X 1 ^ 4 * X 2 ^ 4 + X 1 ^ 8 * X 2 + X 1 ^ 6 * X 2 ^ 3 + X 1 ^ 4 * X 2 ^ 5)) : Poly2) := by
  simp [reduceTwo, CharTwo.sub_eq_add]; ring_nf; simp only [ofNat_mod_poly2]; ring

set_option maxRecDepth 4096 in
theorem pi_1_2 :
    piOperator
      ((poly_literal% Poly2 (X 0 ^ 8 * X 2 + X 0 ^ 6 * X 1 ^ 3 + X 0 ^ 6 * X 1 * X 2 ^ 2 + X 0 ^ 6 * X 2 ^ 3 + X 0 ^ 5 * X 1 ^ 4 + X 0 ^ 5 * X 1 ^ 2 * X 2 ^ 2 + X 0 ^ 5 * X 1 * X 2 ^ 3 + X 0 ^ 4 * X 1 ^ 5 + X 0 ^ 4 * X 1 ^ 4 * X 2 + X 0 ^ 4 * X 1 ^ 3 * X 2 ^ 2 + X 0 ^ 4 * X 1 ^ 2 * X 2 ^ 3 + X 0 ^ 4 * X 1 * X 2 ^ 4 + X 0 ^ 4 * X 2 ^ 5 + X 0 ^ 3 * X 1 ^ 6 + X 0 ^ 3 * X 1 ^ 4 * X 2 ^ 2 + X 0 ^ 3 * X 1 ^ 3 * X 2 ^ 3 + X 0 ^ 2 * X 1 ^ 5 * X 2 ^ 2 + X 0 ^ 2 * X 1 ^ 4 * X 2 ^ 3 + X 0 ^ 2 * X 1 ^ 2 * X 2 ^ 5 + X 0 * X 1 ^ 6 * X 2 ^ 2 + X 0 * X 1 ^ 5 * X 2 ^ 3 + X 0 * X 1 ^ 4 * X 2 ^ 4 + X 1 ^ 8 * X 2 + X 1 ^ 6 * X 2 ^ 3 + X 1 ^ 4 * X 2 ^ 5)) : Poly2) = 0 := by
  simp [piOperator, piSubstitutions]
  ring_nf
  simp [ofNat_mod_poly2]

end TernaryPeriodPolynomials.Argument.ModFourBeta
