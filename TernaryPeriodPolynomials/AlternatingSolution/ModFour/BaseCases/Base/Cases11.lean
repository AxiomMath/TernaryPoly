module

public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Base.Cases
public import TernaryPeriodPolynomials.Tactic.PolynomialLiteral

@[expose] public section


/-! More base cases for the 32-case `W(j,m)` table (continuation; see `BaseCases.lean`
through earlier `BaseCasesN.lean` files). Case (2,0), degree
13: carries only `reduceTwo_g20`.
-/

open MvPolynomial
open TernaryPoly.CharTwoNorm (a b c cplus d7 basis generator)

namespace TernaryPeriodPolynomials.Argument.ModFourBeta

set_option maxRecDepth 4096 in
theorem reduceTwo_g20 :
    reduceTwo
      (poly_literal% (MvPolynomial (Fin 3) ℤ) (40 * X 0 ^ 12 * X 2 - 240 * X 0 ^ 11 * X 1 * X 2 - 328 * X 0 ^ 11 * X 2 ^ 2 + 628 * X 0 ^ 10 * X 1 ^ 2 * X 2 + 1804 * X 0 ^ 10 * X 1 * X 2 ^ 2 + 1034 * X 0 ^ 10 * X 2 ^ 3 - 940 * X 0 ^ 9 * X 1 ^ 3 * X 2 - 4288 * X 0 ^ 9 * X 1 ^ 2 * X 2 ^ 2 - 5170 * X 0 ^ 9 * X 1 * X 2 ^ 3 - 1624 * X 0 ^ 9 * X 2 ^ 4 + 898 * X 0 ^ 8 * X 1 ^ 4 * X 2 + 5766 * X 0 ^ 8 * X 1 ^ 3 * X 2 ^ 2 + 11080 * X 0 ^ 8 * X 1 ^ 2 * X 2 ^ 3 + 7308 * X 0 ^ 8 * X 1 * X 2 ^ 4 + 1416 * X 0 ^ 8 * X 2 ^ 5 - 592 * X 0 ^ 7 * X 1 ^ 5 * X 2 - 4596 * X 0 ^ 7 * X 1 ^ 4 * X 2 ^ 2 - 13300 * X 0 ^ 7 * X 1 ^ 3 * X 2 ^ 3 - 13704 * X 0 ^ 7 * X 1 ^ 2 * X 2 ^ 4 - 5664 * X 0 ^ 7 * X 1 * X 2 ^ 5 - 716 * X 0 ^ 7 * X 2 ^ 6 + 452 * X 0 ^ 6 * X 1 ^ 6 * X 2 + 1806 * X 0 ^ 6 * X 1 ^ 5 * X 2 ^ 2 + 11090 * X 0 ^ 6 * X 1 ^ 4 * X 2 ^ 3 + 13860 * X 0 ^ 6 * X 1 ^ 3 * X 2 ^ 4 + 9586 * X 0 ^ 6 * X 1 ^ 2 * X 2 ^ 5 + 2506 * X 0 ^ 6 * X 1 * X 2 ^ 6 + 208 * X 0 ^ 6 * X 2 ^ 7 - 592 * X 0 ^ 5 * X 1 ^ 7 * X 2 + 1806 * X 0 ^ 5 * X 1 ^ 6 * X 2 ^ 2 - 8434 * X 0 ^ 5 * X 1 ^ 5 * X 2 ^ 3 - 5028 * X 0 ^ 5 * X 1 ^ 4 * X 2 ^ 4 - 8934 * X 0 ^ 5 * X 1 ^ 3 * X 2 ^ 5 - 3222 * X 0 ^ 5 * X 1 ^ 2 * X 2 ^ 6 - 624 * X 0 ^ 5 * X 1 * X 2 ^ 7 - 32 * X 0 ^ 5 * X 2 ^ 8 + 898 * X 0 ^ 4 * X 1 ^ 8 * X 2 - 4596 * X 0 ^ 4 * X 1 ^ 7 * X 2 ^ 2 + 11090 * X 0 ^ 4 * X 1 ^ 6 * X 2 ^ 3 - 5028 * X 0 ^ 4 * X 1 ^ 5 * X 2 ^ 4 + 8608 * X 0 ^ 4 * X 1 ^ 4 * X 2 ^ 5 + 1790 * X 0 ^ 4 * X 1 ^ 3 * X 2 ^ 6 + 864 * X 0 ^ 4 * X 1 ^ 2 * X 2 ^ 7 + 80 * X 0 ^ 4 * X 1 * X 2 ^ 8 + 2 * X 0 ^ 4 * X 2 ^ 9 - 940 * X 0 ^ 3 * X 1 ^ 9 * X 2 + 5766 * X 0 ^ 3 * X 1 ^ 8 * X 2 ^ 2 - 13300 * X 0 ^ 3 * X 1 ^ 7 * X 2 ^ 3 + 13860 * X 0 ^ 3 * X 1 ^ 6 * X 2 ^ 4 - 8934 * X 0 ^ 3 * X 1 ^ 5 * X 2 ^ 5 + 1790 * X 0 ^ 3 * X 1 ^ 4 * X 2 ^ 6 - 688 * X 0 ^ 3 * X 1 ^ 3 * X 2 ^ 7 - 32 * X 0 ^ 3 * X 1 ^ 2 * X 2 ^ 8 - 4 * X 0 ^ 3 * X 1 * X 2 ^ 9 + 628 * X 0 ^ 2 * X 1 ^ 10 * X 2 - 4288 * X 0 ^ 2 * X 1 ^ 9 * X 2 ^ 2 + 11080 * X 0 ^ 2 * X 1 ^ 8 * X 2 ^ 3 - 13704 * X 0 ^ 2 * X 1 ^ 7 * X 2 ^ 4 + 9586 * X 0 ^ 2 * X 1 ^ 6 * X 2 ^ 5 - 3222 * X 0 ^ 2 * X 1 ^ 5 * X 2 ^ 6 + 864 * X 0 ^ 2 * X 1 ^ 4 * X 2 ^ 7 - 32 * X 0 ^ 2 * X 1 ^ 3 * X 2 ^ 8 + 6 * X 0 ^ 2 * X 1 ^ 2 * X 2 ^ 9 - 240 * X 0 * X 1 ^ 11 * X 2 + 1804 * X 0 * X 1 ^ 10 * X 2 ^ 2 - 5170 * X 0 * X 1 ^ 9 * X 2 ^ 3 + 7308 * X 0 * X 1 ^ 8 * X 2 ^ 4 - 5664 * X 0 * X 1 ^ 7 * X 2 ^ 5 + 2506 * X 0 * X 1 ^ 6 * X 2 ^ 6 - 624 * X 0 * X 1 ^ 5 * X 2 ^ 7 + 80 * X 0 * X 1 ^ 4 * X 2 ^ 8 - 4 * X 0 * X 1 ^ 3 * X 2 ^ 9 + 40 * X 1 ^ 12 * X 2 - 328 * X 1 ^ 11 * X 2 ^ 2 + 1034 * X 1 ^ 10 * X 2 ^ 3 - 1624 * X 1 ^ 9 * X 2 ^ 4 + 1416 * X 1 ^ 8 * X 2 ^ 5 - 716 * X 1 ^ 7 * X 2 ^ 6 + 208 * X 1 ^ 6 * X 2 ^ 7 - 32 * X 1 ^ 5 * X 2 ^ 8 + 2 * X 1 ^ 4 * X 2 ^ 9)) =
      (0 : Poly2) := by
  simp [reduceTwo, CharTwo.sub_eq_add]; ring_nf; simp only [ofNat_mod_poly2]; ring

end TernaryPeriodPolynomials.Argument.ModFourBeta
