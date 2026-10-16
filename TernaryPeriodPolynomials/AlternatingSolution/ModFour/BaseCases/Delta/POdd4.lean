module

public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.EbarReduceTwoForms
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Base.Cases
public import TernaryPeriodPolynomials.Polynomial.CharTwo.Reflection

@[expose] public section



/-!
`delta_p (oddGenerator 4) = oddGenerator 0`. Since `kappa 4 = 0`, `oddGenerator 4 = generator 4`
carries no extra `d7` factor.



-/

open MvPolynomial TernaryPoly.CharTwoNorm

namespace TernaryPeriodPolynomials.Argument.ModFourBeta

open PolynomialReflection in
theorem delta_p_odd4_eq_probe : delta_p (oddGenerator 4) = oddGenerator 0 := by
  refine delta_p_eq_of_reflect (ev_oddGenerator 4).symm (ev_oddGenerator 0).symm ?_
  decide +kernel

end TernaryPeriodPolynomials.Argument.ModFourBeta
