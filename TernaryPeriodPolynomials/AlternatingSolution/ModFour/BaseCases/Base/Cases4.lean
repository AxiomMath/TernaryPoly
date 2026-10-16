module

public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Base.Cases
public import TernaryPeriodPolynomials.Tactic.PolynomialLiteral

@[expose] public section


/-! More base cases for the 32-case `W(j,m)` table (continuation; see `BaseCases.lean`,
`BaseCases2.lean`, `BaseCases3.lean`). Case closed here: (0,0), degree
11 — note `reduceTwo` of the halved norm is already literally `0` for this case, so `pi_0_0` is
trivial. -/

open MvPolynomial
open TernaryPoly.CharTwoNorm (a b c cplus d7 basis generator)

namespace TernaryPeriodPolynomials.Argument.ModFourBeta

theorem half_0_0 :
    threeTermNorm (baseSym 0 0) = C 2 *
      (poly_literal% (@MvPolynomial (Fin 3) ℤ CommRing.toCommSemiring) (8 * X 0 ^ 10 * X 2 - 40 * X 0 ^ 9 * X 1 * X 2 - 56 * X 0 ^ 9 * X 2 ^ 2 + 84 * X 0 ^ 8 * X 1 ^ 2 * X 2 + 252 * X 0 ^ 8 * X 1 * X 2 ^ 2 + 138 * X 0 ^ 8 * X 2 ^ 3 - 96 * X 0 ^ 7 * X 1 ^ 3 * X 2 - 468 * X 0 ^ 7 * X 1 ^ 2 * X 2 ^ 2 - 552 * X 0 ^ 7 * X 1 * X 2 ^ 3 - 148 * X 0 ^ 7 * X 2 ^ 4 + 72 * X 0 ^ 6 * X 1 ^ 4 * X 2 + 462 * X 0 ^ 6 * X 1 ^ 3 * X 2 ^ 2 + 918 * X 0 ^ 6 * X 1 ^ 2 * X 2 ^ 3 + 518 * X 0 ^ 6 * X 1 * X 2 ^ 4 + 78 * X 0 ^ 6 * X 2 ^ 5 - 48 * X 0 ^ 5 * X 1 ^ 5 * X 2 - 162 * X 0 ^ 5 * X 1 ^ 4 * X 2 ^ 2 - 822 * X 0 ^ 5 * X 1 ^ 3 * X 2 ^ 3 - 666 * X 0 ^ 5 * X 1 ^ 2 * X 2 ^ 4 - 234 * X 0 ^ 5 * X 1 * X 2 ^ 5 - 20 * X 0 ^ 5 * X 2 ^ 6 + 72 * X 0 ^ 4 * X 1 ^ 6 * X 2 - 162 * X 0 ^ 4 * X 1 ^ 5 * X 2 ^ 2 + 774 * X 0 ^ 4 * X 1 ^ 4 * X 2 ^ 3 + 370 * X 0 ^ 4 * X 1 ^ 3 * X 2 ^ 4 + 318 * X 0 ^ 4 * X 1 ^ 2 * X 2 ^ 5 + 50 * X 0 ^ 4 * X 1 * X 2 ^ 6 + 2 * X 0 ^ 4 * X 2 ^ 7 - 96 * X 0 ^ 3 * X 1 ^ 7 * X 2 + 462 * X 0 ^ 3 * X 1 ^ 6 * X 2 ^ 2 - 822 * X 0 ^ 3 * X 1 ^ 5 * X 2 ^ 3 + 370 * X 0 ^ 3 * X 1 ^ 4 * X 2 ^ 4 - 246 * X 0 ^ 3 * X 1 ^ 3 * X 2 ^ 5 - 20 * X 0 ^ 3 * X 1 ^ 2 * X 2 ^ 6 - 4 * X 0 ^ 3 * X 1 * X 2 ^ 7 + 84 * X 0 ^ 2 * X 1 ^ 8 * X 2 - 468 * X 0 ^ 2 * X 1 ^ 7 * X 2 ^ 2 + 918 * X 0 ^ 2 * X 1 ^ 6 * X 2 ^ 3 - 666 * X 0 ^ 2 * X 1 ^ 5 * X 2 ^ 4 + 318 * X 0 ^ 2 * X 1 ^ 4 * X 2 ^ 5 - 20 * X 0 ^ 2 * X 1 ^ 3 * X 2 ^ 6 + 6 * X 0 ^ 2 * X 1 ^ 2 * X 2 ^ 7 - 40 * X 0 * X 1 ^ 9 * X 2 + 252 * X 0 * X 1 ^ 8 * X 2 ^ 2 - 552 * X 0 * X 1 ^ 7 * X 2 ^ 3 + 518 * X 0 * X 1 ^ 6 * X 2 ^ 4 - 234 * X 0 * X 1 ^ 5 * X 2 ^ 5 + 50 * X 0 * X 1 ^ 4 * X 2 ^ 6 - 4 * X 0 * X 1 ^ 3 * X 2 ^ 7 + 8 * X 1 ^ 10 * X 2 - 56 * X 1 ^ 9 * X 2 ^ 2 + 138 * X 1 ^ 8 * X 2 ^ 3 - 148 * X 1 ^ 7 * X 2 ^ 4 + 78 * X 1 ^ 6 * X 2 ^ 5 - 20 * X 1 ^ 5 * X 2 ^ 6 + 2 * X 1 ^ 4 * X 2 ^ 7)) := by
  simp [baseSym, mult, oddGenLiftSym, genLiftSym, basisLift, kappa, liftD7, liftCplus, liftC,
    liftB, liftA, liftD4, liftD6, threeTermNorm]
  ring

set_option maxRecDepth 4096 in
theorem reduceTwo_g00 :
    reduceTwo
      (poly_literal% (MvPolynomial (Fin 3) ℤ) (8 * X 0 ^ 10 * X 2 - 40 * X 0 ^ 9 * X 1 * X 2 - 56 * X 0 ^ 9 * X 2 ^ 2 + 84 * X 0 ^ 8 * X 1 ^ 2 * X 2 + 252 * X 0 ^ 8 * X 1 * X 2 ^ 2 + 138 * X 0 ^ 8 * X 2 ^ 3 - 96 * X 0 ^ 7 * X 1 ^ 3 * X 2 - 468 * X 0 ^ 7 * X 1 ^ 2 * X 2 ^ 2 - 552 * X 0 ^ 7 * X 1 * X 2 ^ 3 - 148 * X 0 ^ 7 * X 2 ^ 4 + 72 * X 0 ^ 6 * X 1 ^ 4 * X 2 + 462 * X 0 ^ 6 * X 1 ^ 3 * X 2 ^ 2 + 918 * X 0 ^ 6 * X 1 ^ 2 * X 2 ^ 3 + 518 * X 0 ^ 6 * X 1 * X 2 ^ 4 + 78 * X 0 ^ 6 * X 2 ^ 5 - 48 * X 0 ^ 5 * X 1 ^ 5 * X 2 - 162 * X 0 ^ 5 * X 1 ^ 4 * X 2 ^ 2 - 822 * X 0 ^ 5 * X 1 ^ 3 * X 2 ^ 3 - 666 * X 0 ^ 5 * X 1 ^ 2 * X 2 ^ 4 - 234 * X 0 ^ 5 * X 1 * X 2 ^ 5 - 20 * X 0 ^ 5 * X 2 ^ 6 + 72 * X 0 ^ 4 * X 1 ^ 6 * X 2 - 162 * X 0 ^ 4 * X 1 ^ 5 * X 2 ^ 2 + 774 * X 0 ^ 4 * X 1 ^ 4 * X 2 ^ 3 + 370 * X 0 ^ 4 * X 1 ^ 3 * X 2 ^ 4 + 318 * X 0 ^ 4 * X 1 ^ 2 * X 2 ^ 5 + 50 * X 0 ^ 4 * X 1 * X 2 ^ 6 + 2 * X 0 ^ 4 * X 2 ^ 7 - 96 * X 0 ^ 3 * X 1 ^ 7 * X 2 + 462 * X 0 ^ 3 * X 1 ^ 6 * X 2 ^ 2 - 822 * X 0 ^ 3 * X 1 ^ 5 * X 2 ^ 3 + 370 * X 0 ^ 3 * X 1 ^ 4 * X 2 ^ 4 - 246 * X 0 ^ 3 * X 1 ^ 3 * X 2 ^ 5 - 20 * X 0 ^ 3 * X 1 ^ 2 * X 2 ^ 6 - 4 * X 0 ^ 3 * X 1 * X 2 ^ 7 + 84 * X 0 ^ 2 * X 1 ^ 8 * X 2 - 468 * X 0 ^ 2 * X 1 ^ 7 * X 2 ^ 2 + 918 * X 0 ^ 2 * X 1 ^ 6 * X 2 ^ 3 - 666 * X 0 ^ 2 * X 1 ^ 5 * X 2 ^ 4 + 318 * X 0 ^ 2 * X 1 ^ 4 * X 2 ^ 5 - 20 * X 0 ^ 2 * X 1 ^ 3 * X 2 ^ 6 + 6 * X 0 ^ 2 * X 1 ^ 2 * X 2 ^ 7 - 40 * X 0 * X 1 ^ 9 * X 2 + 252 * X 0 * X 1 ^ 8 * X 2 ^ 2 - 552 * X 0 * X 1 ^ 7 * X 2 ^ 3 + 518 * X 0 * X 1 ^ 6 * X 2 ^ 4 - 234 * X 0 * X 1 ^ 5 * X 2 ^ 5 + 50 * X 0 * X 1 ^ 4 * X 2 ^ 6 - 4 * X 0 * X 1 ^ 3 * X 2 ^ 7 + 8 * X 1 ^ 10 * X 2 - 56 * X 1 ^ 9 * X 2 ^ 2 + 138 * X 1 ^ 8 * X 2 ^ 3 - 148 * X 1 ^ 7 * X 2 ^ 4 + 78 * X 1 ^ 6 * X 2 ^ 5 - 20 * X 1 ^ 5 * X 2 ^ 6 + 2 * X 1 ^ 4 * X 2 ^ 7)) =
      (0 : Poly2) := by
  simp [reduceTwo, CharTwo.sub_eq_add]; ring_nf; simp only [ofNat_mod_poly2]; ring

set_option maxRecDepth 4096 in
theorem pi_0_0 :
    piOperator
      (0 : Poly2) = 0 := by
  simp [piOperator, piSubstitutions]

end TernaryPeriodPolynomials.Argument.ModFourBeta
