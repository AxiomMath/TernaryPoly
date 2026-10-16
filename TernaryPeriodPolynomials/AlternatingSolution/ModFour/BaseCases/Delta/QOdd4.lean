module

public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.EbarReduceTwoForms
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Base.Cases
public import TernaryPeriodPolynomials.Polynomial.CharTwo.Reflection

@[expose] public section



open MvPolynomial TernaryPoly.CharTwoNorm

namespace TernaryPeriodPolynomials.Argument.ModFourBeta

open PolynomialReflection in
theorem delta_q_odd4_eq_probe : delta_q (oddGenerator 4) = oddGenerator 2 := by
  refine delta_q_eq_of_reflect (ev_oddGenerator 4).symm (ev_oddGenerator 2).symm ?_
  decide +kernel

end TernaryPeriodPolynomials.Argument.ModFourBeta
