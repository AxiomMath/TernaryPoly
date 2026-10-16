module

public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Delta.KappaOneReduction
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Delta.QGen0

@[expose] public section


/-!
`delta_q (oddGenerator 0) = 0`, by the same kappa-one-lift composition as
`DeltaPOdd0.lean`: lift `delta_q_gen0_probe` through `delta_q_oddGenerator_kappa_one`
(valid since `kappa 0 = 1`), then close the resulting `d7 * 0 = 0` with `mul_zero`.
-/

open MvPolynomial TernaryPoly.CharTwoNorm

namespace TernaryPeriodPolynomials.Argument.ModFourBeta

theorem delta_q_odd0_eq_probe : delta_q (oddGenerator 0) = 0 := by
  have hk0 : kappa 0 = 1 := by simp [kappa]
  rw [delta_q_oddGenerator_kappa_one hk0, delta_q_gen0_probe, mul_zero]

end TernaryPeriodPolynomials.Argument.ModFourBeta
