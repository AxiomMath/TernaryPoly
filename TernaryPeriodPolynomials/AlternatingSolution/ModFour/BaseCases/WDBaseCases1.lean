module

public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.WDBaseCasesCore

@[expose] public section



open MvPolynomial
open TernaryPoly.CharTwoNorm (a b c cplus d7 basis generator)

namespace TernaryPeriodPolynomials.Argument.ModFourBeta

/-! Case `j = 1`: `piOperator (reduceTwo (threeTermNorm (WD 1))) = oddGenerator 1`. -/

private theorem core_1 :
    piOperator (TernaryPoly.CharTwoNorm.norm (reduceTwo (W 1))) = generator 1 :=
  core_of_reflect 1 (by decide +kernel)

theorem pi_reduceTwo_threeTermNorm_WD_1 :
    piOperator (reduceTwo (threeTermNorm (WD 1))) = oddGenerator 1 :=
  pi_reduceTwo_threeTermNorm_WD_of_core core_1

end TernaryPeriodPolynomials.Argument.ModFourBeta
