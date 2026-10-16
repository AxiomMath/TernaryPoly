module

public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.WDBaseCasesCore

@[expose] public section



open MvPolynomial
open TernaryPoly.CharTwoNorm (a b c cplus d7 basis generator)

namespace TernaryPeriodPolynomials.Argument.ModFourBeta

/-! Case `j = 2`: `piOperator (reduceTwo (threeTermNorm (WD 2))) = oddGenerator 2`. -/

private theorem core_2 :
    piOperator (TernaryPoly.CharTwoNorm.norm (reduceTwo (W 2))) = generator 2 :=
  core_of_reflect 2 (by decide +kernel)

theorem pi_reduceTwo_threeTermNorm_WD_2 :
    piOperator (reduceTwo (threeTermNorm (WD 2))) = oddGenerator 2 :=
  pi_reduceTwo_threeTermNorm_WD_of_core core_2

end TernaryPeriodPolynomials.Argument.ModFourBeta
