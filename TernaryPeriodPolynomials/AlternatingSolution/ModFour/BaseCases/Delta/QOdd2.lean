module

public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Delta.KappaOneReduction
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Delta.QGen2

@[expose] public section


/-!
`delta_q (oddGenerator 2) = 0`, by the same kappa-one-lift composition as
`DeltaPOdd2.lean`: lift `delta_q_gen2_probe` through `delta_q_oddGenerator_kappa_one`
(valid since `kappa 2 = 1`), then close the resulting `d7 * 0 = 0` with `mul_zero`.
-/

open MvPolynomial TernaryPoly.CharTwoNorm

namespace TernaryPeriodPolynomials.Argument.ModFourBeta

theorem delta_q_odd2_eq_probe : delta_q (oddGenerator 2) = 0 := by
  have hk2 : kappa 2 = 1 := by simp [kappa]
  rw [delta_q_oddGenerator_kappa_one hk2, delta_q_gen2_probe, mul_zero]

end TernaryPeriodPolynomials.Argument.ModFourBeta
