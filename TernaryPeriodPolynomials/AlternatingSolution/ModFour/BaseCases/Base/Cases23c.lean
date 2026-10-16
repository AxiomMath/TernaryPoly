module

public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Base.Cases
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Base.Cases23Parts
public import TernaryPeriodPolynomials.Tactic.PolynomialLiteral

@[expose] public section


/-! Case (7,0): the mod-two reduction `reduceTwo_g70`. The
`reduceTwo` argument is stated via the same `g70_part1 .. g70_part7` split used by
`half_7_0` (`BaseCases23.lean`).
-/

open MvPolynomial
open TernaryPoly.CharTwoNorm (a b c cplus d7 basis generator)

namespace TernaryPeriodPolynomials.Argument.ModFourBeta

set_option maxRecDepth 4000

theorem reduceTwo_g70 :
    reduceTwo
      (g70_part1 + g70_part2 + g70_part3 + g70_part4 + g70_part5 + g70_part6 + g70_part7) =
      ((poly_literal% Poly2 (X 0 ^ 2 * X 1 ^ 4 * X 2 ^ 11 + X 0 ^ 2 * X 1 ^ 6 * X 2 ^ 9 + X 0 ^ 2 * X 1 ^ 10 * X 2 ^ 5 +
        X 0 ^ 2 * X 1 ^ 12 * X 2 ^ 3 + X 0 ^ 3 * X 1 ^ 5 * X 2 ^ 9 + X 0 ^ 3 * X 1 ^ 9 * X 2 ^ 5 +
        X 0 ^ 4 * X 1 ^ 2 * X 2 ^ 11 + X 0 ^ 4 * X 1 ^ 12 * X 2 + X 0 ^ 5 * X 1 ^ 3 * X 2 ^ 9 + X 0 ^ 5 * X 1 ^ 9 * X 2 ^ 3 +
        X 0 ^ 6 * X 1 ^ 2 * X 2 ^ 9 + X 0 ^ 6 * X 1 ^ 10 * X 2 + X 0 ^ 9 * X 1 ^ 3 * X 2 ^ 5 + X 0 ^ 9 * X 1 ^ 5 * X 2 ^ 3 +
        X 0 ^ 10 * X 1 ^ 2 * X 2 ^ 5 + X 0 ^ 10 * X 1 ^ 6 * X 2 + X 0 ^ 12 * X 1 ^ 2 * X 2 ^ 3 +
        X 0 ^ 12 * X 1 ^ 4 * X 2)) : Poly2) := by
  simp [reduceTwo, CharTwo.sub_eq_add, g70_part1, g70_part2, g70_part3, g70_part4, g70_part5,
    g70_part6, g70_part7]
  ring_nf
  simp only [ofNat_mod_poly2]
  ring

end TernaryPeriodPolynomials.Argument.ModFourBeta
