module

public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.WDBaseCasesCore

@[expose] public section



open MvPolynomial
open TernaryPoly.CharTwoNorm (a b c cplus d7 basis generator)

namespace TernaryPeriodPolynomials.Argument.ModFourBeta

/-! Case `j = 4`: `piOperator (reduceTwo (threeTermNorm (WD 4))) = oddGenerator 4`. -/

private theorem core_4 :
    piOperator (TernaryPoly.CharTwoNorm.norm (reduceTwo (W 4))) = generator 4 :=
  core_of_reflect 4 (by decide +kernel)

theorem pi_reduceTwo_threeTermNorm_WD_4 :
    piOperator (reduceTwo (threeTermNorm (WD 4))) = oddGenerator 4 :=
  pi_reduceTwo_threeTermNorm_WD_of_core core_4

end TernaryPeriodPolynomials.Argument.ModFourBeta
