module

public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.WDBaseCasesCore

@[expose] public section



open MvPolynomial
open TernaryPoly.CharTwoNorm (a b c cplus d7 basis generator)

namespace TernaryPeriodPolynomials.Argument.ModFourBeta

/-! Case `j = 6`: `piOperator (reduceTwo (threeTermNorm (WD 6))) = oddGenerator 6`. -/

private theorem core_6 :
    piOperator (TernaryPoly.CharTwoNorm.norm (reduceTwo (W 6))) = generator 6 :=
  core_of_reflect 6 (by decide +kernel)

theorem pi_reduceTwo_threeTermNorm_WD_6 :
    piOperator (reduceTwo (threeTermNorm (WD 6))) = oddGenerator 6 :=
  pi_reduceTwo_threeTermNorm_WD_of_core core_6

end TernaryPeriodPolynomials.Argument.ModFourBeta
