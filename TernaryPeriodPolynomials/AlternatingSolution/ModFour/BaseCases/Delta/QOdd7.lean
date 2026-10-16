module

public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Delta.KappaOneReduction
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Delta.QGen7Combine
public import TernaryPeriodPolynomials.Polynomial.CharTwo.Reflection

@[expose] public section


/-!
`delta_q (oddGenerator 7) = d7 ^ 2 * oddGenerator 6`, by the same kappa-one-lift composition:
lift `delta_q_gen7` through `delta_q_oddGenerator_kappa_one` (valid since `kappa 7 = 1`),
then close with `ring`.
-/

open MvPolynomial TernaryPoly.CharTwoNorm

namespace TernaryPeriodPolynomials.Argument.ModFourBeta

open PolynomialReflection in
theorem delta_q_odd7_eq_probe : delta_q (oddGenerator 7) = d7 ^ 2 * oddGenerator 6 := by
  refine delta_q_eq_of_reflect (ev_oddGenerator 7).symm (lQ := mulL (powL d7L 2) (oddGeneratorL 6)) (by simp only [ev_mulL, ev_powL, ev_d7, ev_oddGenerator]) ?_
  decide +kernel

end TernaryPeriodPolynomials.Argument.ModFourBeta
