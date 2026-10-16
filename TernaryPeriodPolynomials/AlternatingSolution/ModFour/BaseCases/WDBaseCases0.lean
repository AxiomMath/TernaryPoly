module

public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.WDBaseCasesCore

@[expose] public section



open MvPolynomial
open TernaryPoly.CharTwoNorm (a b c cplus d7 basis generator)

namespace TernaryPeriodPolynomials.Argument.ModFourBeta

/-! Case `j = 0`: `piOperator (reduceTwo (threeTermNorm (WD 0))) = oddGenerator 0`. -/

private theorem core_0 :
    piOperator (TernaryPoly.CharTwoNorm.norm (reduceTwo (W 0))) = generator 0 :=
  core_of_reflect 0 (by decide +kernel)

theorem pi_reduceTwo_threeTermNorm_WD_0 :
    piOperator (reduceTwo (threeTermNorm (WD 0))) = oddGenerator 0 :=
  pi_reduceTwo_threeTermNorm_WD_of_core core_0

end TernaryPeriodPolynomials.Argument.ModFourBeta
