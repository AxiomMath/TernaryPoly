module

public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.EbarReduceTwoForms
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Base.Cases
public import TernaryPeriodPolynomials.Polynomial.CharTwo.Reflection

@[expose] public section



/-!
`delta_q (oddGenerator 6) = 0`, by direct computation (`kappa 6 = 0`, same reasoning as
`DeltaPOdd6.lean`).
-/

open MvPolynomial TernaryPoly.CharTwoNorm

namespace TernaryPeriodPolynomials.Argument.ModFourBeta

open PolynomialReflection in
theorem delta_q_odd6_eq_probe : delta_q (oddGenerator 6) = 0 := by
  refine delta_q_eq_of_reflect (ev_oddGenerator 6).symm (lQ := []) rfl ?_
  decide +kernel

end TernaryPeriodPolynomials.Argument.ModFourBeta
