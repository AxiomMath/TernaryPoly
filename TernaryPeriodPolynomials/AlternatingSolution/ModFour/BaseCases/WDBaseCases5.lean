module

public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.WDBaseCasesCore

@[expose] public section



open MvPolynomial
open TernaryPoly.CharTwoNorm (a b c cplus d7 basis generator)

namespace TernaryPeriodPolynomials.Argument.ModFourBeta

/-! Case `j = 5`: `piOperator (reduceTwo (threeTermNorm (WD 5))) = oddGenerator 5`. -/

private theorem core_5 :
    piOperator (TernaryPoly.CharTwoNorm.norm (reduceTwo (W 5))) = generator 5 :=
  core_of_reflect 5 (by decide +kernel)

theorem pi_reduceTwo_threeTermNorm_WD_5 :
    piOperator (reduceTwo (threeTermNorm (WD 5))) = oddGenerator 5 :=
  pi_reduceTwo_threeTermNorm_WD_of_core core_5

end TernaryPeriodPolynomials.Argument.ModFourBeta
