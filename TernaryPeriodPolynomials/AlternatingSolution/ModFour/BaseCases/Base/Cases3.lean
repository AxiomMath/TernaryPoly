module

public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Base.Cases
public import TernaryPeriodPolynomials.Tactic.PolynomialLiteral

@[expose] public section


/-! More base cases for the 32-case `W(j,m)` table (continuation; see `BaseCases.lean` and
`BaseCases2.lean`). Cases closed in this file: (6,0), as the three facts
`half_6_0`/`reduceTwo_g60`/`pi_6_0` (no bundled `case_j_m`; see `BaseCases2.lean`'s header for the
rationale). -/

open MvPolynomial
open TernaryPoly.CharTwoNorm (a b c cplus d7 basis generator)

namespace TernaryPeriodPolynomials.Argument.ModFourBeta

theorem half_6_0 :
    threeTermNorm (baseSym 6 0) = C 2 *
      (poly_literal% (@MvPolynomial (Fin 3) ℤ CommRing.toCommSemiring) (-80 * X 0 ^ 9 + 360 * X 0 ^ 8 * X 1 + 497 * X 0 ^ 8 * X 2 - 684 * X 0 ^ 7 * X 1 ^ 2 - 1988 * X 0 ^ 7 * X 1 * X 2 - 1168 * X 0 ^ 7 * X 2 ^ 2 + 714 * X 0 ^ 6 * X 1 ^ 3 + 3539 * X 0 ^ 6 * X 1 ^ 2 * X 2 + 4088 * X 0 ^ 6 * X 1 * X 2 ^ 2 + 1482 * X 0 ^ 6 * X 2 ^ 3 - 270 * X 0 ^ 5 * X 1 ^ 4 - 3659 * X 0 ^ 5 * X 1 ^ 3 * X 2 - 5256 * X 0 ^ 5 * X 1 ^ 2 * X 2 ^ 2 - 4446 * X 0 ^ 5 * X 1 * X 2 ^ 3 - 1008 * X 0 ^ 5 * X 2 ^ 4 - 270 * X 0 ^ 4 * X 1 ^ 5 + 3719 * X 0 ^ 4 * X 1 ^ 4 * X 2 + 2920 * X 0 ^ 4 * X 1 ^ 3 * X 2 ^ 2 + 6768 * X 0 ^ 4 * X 1 ^ 2 * X 2 ^ 3 + 2520 * X 0 ^ 4 * X 1 * X 2 ^ 4 + 506 * X 0 ^ 4 * X 2 ^ 5 + 714 * X 0 ^ 3 * X 1 ^ 6 - 3659 * X 0 ^ 3 * X 1 ^ 5 * X 2 + 2920 * X 0 ^ 3 * X 1 ^ 4 * X 2 ^ 2 - 6126 * X 0 ^ 3 * X 1 ^ 3 * X 2 ^ 3 - 1008 * X 0 ^ 3 * X 1 ^ 2 * X 2 ^ 4 - 1012 * X 0 ^ 3 * X 1 * X 2 ^ 5 - 94 * X 0 ^ 3 * X 2 ^ 6 - 684 * X 0 ^ 2 * X 1 ^ 7 + 3539 * X 0 ^ 2 * X 1 ^ 6 * X 2 - 5256 * X 0 ^ 2 * X 1 ^ 5 * X 2 ^ 2 + 6768 * X 0 ^ 2 * X 1 ^ 4 * X 2 ^ 3 - 1008 * X 0 ^ 2 * X 1 ^ 3 * X 2 ^ 4 + 1518 * X 0 ^ 2 * X 1 ^ 2 * X 2 ^ 5 + 141 * X 0 ^ 2 * X 1 * X 2 ^ 6 + 25 * X 0 ^ 2 * X 2 ^ 7 + 360 * X 0 * X 1 ^ 8 - 1988 * X 0 * X 1 ^ 7 * X 2 + 4088 * X 0 * X 1 ^ 6 * X 2 ^ 2 - 4446 * X 0 * X 1 ^ 5 * X 2 ^ 3 + 2520 * X 0 * X 1 ^ 4 * X 2 ^ 4 - 1012 * X 0 * X 1 ^ 3 * X 2 ^ 5 + 141 * X 0 * X 1 ^ 2 * X 2 ^ 6 - 25 * X 0 * X 1 * X 2 ^ 7 - 80 * X 1 ^ 9 + 497 * X 1 ^ 8 * X 2 - 1168 * X 1 ^ 7 * X 2 ^ 2 + 1482 * X 1 ^ 6 * X 2 ^ 3 - 1008 * X 1 ^ 5 * X 2 ^ 4 + 506 * X 1 ^ 4 * X 2 ^ 5 - 94 * X 1 ^ 3 * X 2 ^ 6 + 25 * X 1 ^ 2 * X 2 ^ 7)) := by
  simp [baseSym, mult, oddGenLiftSym, genLiftSym, basisLift, kappa, liftD7, liftCplus, liftC,
    liftB, liftA, liftD4, liftD6, threeTermNorm]
  ring

set_option maxRecDepth 4096 in
theorem reduceTwo_g60 :
    reduceTwo
      (poly_literal% (MvPolynomial (Fin 3) ℤ) (-80 * X 0 ^ 9 + 360 * X 0 ^ 8 * X 1 + 497 * X 0 ^ 8 * X 2 - 684 * X 0 ^ 7 * X 1 ^ 2 - 1988 * X 0 ^ 7 * X 1 * X 2 - 1168 * X 0 ^ 7 * X 2 ^ 2 + 714 * X 0 ^ 6 * X 1 ^ 3 + 3539 * X 0 ^ 6 * X 1 ^ 2 * X 2 + 4088 * X 0 ^ 6 * X 1 * X 2 ^ 2 + 1482 * X 0 ^ 6 * X 2 ^ 3 - 270 * X 0 ^ 5 * X 1 ^ 4 - 3659 * X 0 ^ 5 * X 1 ^ 3 * X 2 - 5256 * X 0 ^ 5 * X 1 ^ 2 * X 2 ^ 2 - 4446 * X 0 ^ 5 * X 1 * X 2 ^ 3 - 1008 * X 0 ^ 5 * X 2 ^ 4 - 270 * X 0 ^ 4 * X 1 ^ 5 + 3719 * X 0 ^ 4 * X 1 ^ 4 * X 2 + 2920 * X 0 ^ 4 * X 1 ^ 3 * X 2 ^ 2 + 6768 * X 0 ^ 4 * X 1 ^ 2 * X 2 ^ 3 + 2520 * X 0 ^ 4 * X 1 * X 2 ^ 4 + 506 * X 0 ^ 4 * X 2 ^ 5 + 714 * X 0 ^ 3 * X 1 ^ 6 - 3659 * X 0 ^ 3 * X 1 ^ 5 * X 2 + 2920 * X 0 ^ 3 * X 1 ^ 4 * X 2 ^ 2 - 6126 * X 0 ^ 3 * X 1 ^ 3 * X 2 ^ 3 - 1008 * X 0 ^ 3 * X 1 ^ 2 * X 2 ^ 4 - 1012 * X 0 ^ 3 * X 1 * X 2 ^ 5 - 94 * X 0 ^ 3 * X 2 ^ 6 - 684 * X 0 ^ 2 * X 1 ^ 7 + 3539 * X 0 ^ 2 * X 1 ^ 6 * X 2 - 5256 * X 0 ^ 2 * X 1 ^ 5 * X 2 ^ 2 + 6768 * X 0 ^ 2 * X 1 ^ 4 * X 2 ^ 3 - 1008 * X 0 ^ 2 * X 1 ^ 3 * X 2 ^ 4 + 1518 * X 0 ^ 2 * X 1 ^ 2 * X 2 ^ 5 + 141 * X 0 ^ 2 * X 1 * X 2 ^ 6 + 25 * X 0 ^ 2 * X 2 ^ 7 + 360 * X 0 * X 1 ^ 8 - 1988 * X 0 * X 1 ^ 7 * X 2 + 4088 * X 0 * X 1 ^ 6 * X 2 ^ 2 - 4446 * X 0 * X 1 ^ 5 * X 2 ^ 3 + 2520 * X 0 * X 1 ^ 4 * X 2 ^ 4 - 1012 * X 0 * X 1 ^ 3 * X 2 ^ 5 + 141 * X 0 * X 1 ^ 2 * X 2 ^ 6 - 25 * X 0 * X 1 * X 2 ^ 7 - 80 * X 1 ^ 9 + 497 * X 1 ^ 8 * X 2 - 1168 * X 1 ^ 7 * X 2 ^ 2 + 1482 * X 1 ^ 6 * X 2 ^ 3 - 1008 * X 1 ^ 5 * X 2 ^ 4 + 506 * X 1 ^ 4 * X 2 ^ 5 - 94 * X 1 ^ 3 * X 2 ^ 6 + 25 * X 1 ^ 2 * X 2 ^ 7)) =
      ((poly_literal% Poly2 (X 0 ^ 8 * X 2 + X 0 ^ 6 * X 1 ^ 2 * X 2 + X 0 ^ 5 * X 1 ^ 3 * X 2 + X 0 ^ 4 * X 1 ^ 4 * X 2 + X 0 ^ 3 * X 1 ^ 5 * X 2 + X 0 ^ 2 * X 1 ^ 6 * X 2 + X 0 ^ 2 * X 1 * X 2 ^ 6 + X 0 ^ 2 * X 2 ^ 7 + X 0 * X 1 ^ 2 * X 2 ^ 6 + X 0 * X 1 * X 2 ^ 7 + X 1 ^ 8 * X 2 + X 1 ^ 2 * X 2 ^ 7)) : Poly2) := by
  simp [reduceTwo, CharTwo.sub_eq_add]; ring_nf; simp only [ofNat_mod_poly2]; ring

set_option maxRecDepth 4096 in
theorem pi_6_0 :
    piOperator
      ((poly_literal% Poly2 (X 0 ^ 8 * X 2 + X 0 ^ 6 * X 1 ^ 2 * X 2 + X 0 ^ 5 * X 1 ^ 3 * X 2 + X 0 ^ 4 * X 1 ^ 4 * X 2 + X 0 ^ 3 * X 1 ^ 5 * X 2 + X 0 ^ 2 * X 1 ^ 6 * X 2 + X 0 ^ 2 * X 1 * X 2 ^ 6 + X 0 ^ 2 * X 2 ^ 7 + X 0 * X 1 ^ 2 * X 2 ^ 6 + X 0 * X 1 * X 2 ^ 7 + X 1 ^ 8 * X 2 + X 1 ^ 2 * X 2 ^ 7)) : Poly2) = 0 := by
  simp [piOperator, piSubstitutions]
  ring_nf
  simp [ofNat_mod_poly2]

end TernaryPeriodPolynomials.Argument.ModFourBeta
