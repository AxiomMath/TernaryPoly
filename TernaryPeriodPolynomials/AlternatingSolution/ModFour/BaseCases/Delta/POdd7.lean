module

public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Delta.KappaOneReduction
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Delta.PGen7
public import TernaryPeriodPolynomials.Polynomial.CharTwo.Reflection

@[expose] public section


/-!
`delta_p (oddGenerator 7) = d7 ^ 2 * oddGenerator 4`, by the same kappa-one-lift composition:
lift `delta_p_gen7_probe` through `delta_p_oddGenerator_kappa_one` (valid since `kappa 7 = 1`),
then close with `ring`.
-/

open MvPolynomial TernaryPoly.CharTwoNorm

namespace TernaryPeriodPolynomials.Argument.ModFourBeta

open PolynomialReflection in
theorem delta_p_odd7_eq_probe : delta_p (oddGenerator 7) = d7 ^ 2 * oddGenerator 4 := by
  refine delta_p_eq_of_reflect (ev_oddGenerator 7).symm (lQ := mulL (powL d7L 2) (oddGeneratorL 4)) (by simp only [ev_mulL, ev_powL, ev_d7, ev_oddGenerator]) ?_
  decide +kernel

end TernaryPeriodPolynomials.Argument.ModFourBeta
