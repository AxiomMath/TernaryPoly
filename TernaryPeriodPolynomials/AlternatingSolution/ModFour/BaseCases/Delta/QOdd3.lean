module

public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.EbarReduceTwoForms
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Base.Cases
public import TernaryPeriodPolynomials.Polynomial.CharTwo.Reflection

@[expose] public section



/-!
`delta_q (oddGenerator 3) = 0`, by direct computation (`kappa 3 = 0`, same reasoning as
`DeltaPOdd3.lean`).
-/

open MvPolynomial TernaryPoly.CharTwoNorm

namespace TernaryPeriodPolynomials.Argument.ModFourBeta

open PolynomialReflection in
theorem delta_q_odd3_eq_probe : delta_q (oddGenerator 3) = 0 := by
  refine delta_q_eq_of_reflect (ev_oddGenerator 3).symm (lQ := []) rfl ?_
  decide +kernel

end TernaryPeriodPolynomials.Argument.ModFourBeta
