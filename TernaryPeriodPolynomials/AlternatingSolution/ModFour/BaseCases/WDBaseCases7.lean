module

public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.WDBaseCasesCore

@[expose] public section



open MvPolynomial
open TernaryPoly.CharTwoNorm (a b c cplus d7 basis generator)

namespace TernaryPeriodPolynomials.Argument.ModFourBeta

/-! Case `j = 7`: `piOperator (reduceTwo (threeTermNorm (WD 7))) = oddGenerator 7`. -/

private theorem core_7 :
    piOperator (TernaryPoly.CharTwoNorm.norm (reduceTwo (W 7))) = generator 7 :=
  core_of_reflect 7 (by decide +kernel)

theorem pi_reduceTwo_threeTermNorm_WD_7 :
    piOperator (reduceTwo (threeTermNorm (WD 7))) = oddGenerator 7 :=
  pi_reduceTwo_threeTermNorm_WD_of_core core_7

end TernaryPeriodPolynomials.Argument.ModFourBeta
