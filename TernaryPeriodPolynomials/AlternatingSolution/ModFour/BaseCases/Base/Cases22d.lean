module

public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Base.Cases
public import TernaryPeriodPolynomials.Tactic.PolynomialLiteral

@[expose] public section


/-! Case (5,0): the `piOperator` vanishing fact `pi_5_0`. -/

open MvPolynomial
open TernaryPoly.CharTwoNorm (a b c cplus d7 basis generator)

namespace TernaryPeriodPolynomials.Argument.ModFourBeta

set_option maxRecDepth 4000

theorem pi_5_0 :
    piOperator
      ((poly_literal% Poly2 (X 0 ^ 2 * X 1 ^ 6 * X 2 ^ 7 + X 0 ^ 2 * X 1 ^ 10 * X 2 ^ 3 + X 0 ^ 3 * X 1 ^ 5 * X 2 ^ 7 +
       X 0 ^ 3 * X 1 ^ 9 * X 2 ^ 3 + X 0 ^ 4 * X 1 ^ 8 * X 2 ^ 3 + X 0 ^ 4 * X 1 ^ 10 * X 2 +
       X 0 ^ 5 * X 1 ^ 3 * X 2 ^ 7 + X 0 ^ 5 * X 1 ^ 9 * X 2 + X 0 ^ 6 * X 1 ^ 2 * X 2 ^ 7 +
       X 0 ^ 6 * X 1 ^ 8 * X 2 + X 0 ^ 8 * X 1 ^ 4 * X 2 ^ 3 + X 0 ^ 8 * X 1 ^ 6 * X 2 +
       X 0 ^ 9 * X 1 ^ 3 * X 2 ^ 3 + X 0 ^ 9 * X 1 ^ 5 * X 2 + X 0 ^ 10 * X 1 ^ 2 * X 2 ^ 3 +
       X 0 ^ 10 * X 1 ^ 4 * X 2)) : Poly2) = 0 := by
  simp [piOperator, piSubstitutions]
  ring_nf
  simp [ofNat_mod_poly2]

end TernaryPeriodPolynomials.Argument.ModFourBeta
