module

public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.EbarReduceTwoForms
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Base.Cases
public import TernaryPeriodPolynomials.Polynomial.CharTwo.Reflection

@[expose] public section



open MvPolynomial TernaryPoly.CharTwoNorm

namespace TernaryPeriodPolynomials.Argument.ModFourBeta

open PolynomialReflection in
theorem delta_p_gen0_probe : delta_p (generator 0) = 0 := by
  refine delta_p_eq_of_reflect (ev_generator 0).symm (lQ := []) rfl ?_
  decide +kernel

end TernaryPeriodPolynomials.Argument.ModFourBeta
