module

public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Delta.KappaOneReduction
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Delta.QGen5
public import TernaryPeriodPolynomials.Polynomial.CharTwo.Reflection

@[expose] public section


/-!
`delta_q (oddGenerator 5) = d7 ^ 2 * (oddGenerator 3 + oddGenerator 4)`, by the same
kappa-one-lift composition as `DeltaPOdd5.lean`: lift `delta_q_gen5_probe` through
`delta_q_oddGenerator_kappa_one` (valid since `kappa 5 = 1`), then close with `ring`.
-/

open MvPolynomial TernaryPoly.CharTwoNorm

namespace TernaryPeriodPolynomials.Argument.ModFourBeta

open PolynomialReflection in
theorem delta_q_odd5_eq_probe : delta_q (oddGenerator 5) = d7 ^ 2 * (oddGenerator 3 + oddGenerator 4) := by
  refine delta_q_eq_of_reflect (ev_oddGenerator 5).symm (lQ := mulL (powL d7L 2) (addL (oddGeneratorL 3) (oddGeneratorL 4))) (by simp only [ev_mulL, ev_powL, ev_addL, ev_d7, ev_oddGenerator]) ?_
  decide +kernel

end TernaryPeriodPolynomials.Argument.ModFourBeta
