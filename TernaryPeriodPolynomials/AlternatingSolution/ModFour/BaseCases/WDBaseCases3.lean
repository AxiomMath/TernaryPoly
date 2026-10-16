module

public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.WDBaseCasesCore

@[expose] public section



open MvPolynomial
open TernaryPoly.CharTwoNorm (a b c cplus d7 basis generator)

namespace TernaryPeriodPolynomials.Argument.ModFourBeta

/-! Case `j = 3`: `piOperator (reduceTwo (threeTermNorm (WD 3))) = oddGenerator 3`. -/

private theorem core_3 :
    piOperator (TernaryPoly.CharTwoNorm.norm (reduceTwo (W 3))) = generator 3 :=
  core_of_reflect 3 (by decide +kernel)

theorem pi_reduceTwo_threeTermNorm_WD_3 :
    piOperator (reduceTwo (threeTermNorm (WD 3))) = oddGenerator 3 :=
  pi_reduceTwo_threeTermNorm_WD_of_core core_3

end TernaryPeriodPolynomials.Argument.ModFourBeta
