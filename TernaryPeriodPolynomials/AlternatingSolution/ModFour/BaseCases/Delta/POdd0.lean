module

public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Delta.KappaOneReduction
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Delta.PGen0

@[expose] public section


/-!
`delta_p (oddGenerator 0) = 0`, by the kappa-one-lift composition: lift the generator-level fact `delta_p_gen0_probe` through `delta_p_oddGenerator_kappa_one`
(valid since `kappa 0 = 1`). The extra `d7` factor from the lift multiplies through a
zero right-hand side, so (unlike the nonzero `oddGenerator 5`/`oddGenerator 7` cases) no
`ring` normalization against a large explicit polynomial is needed to close the goal.
-/

open MvPolynomial TernaryPoly.CharTwoNorm

namespace TernaryPeriodPolynomials.Argument.ModFourBeta

theorem delta_p_odd0_eq_probe : delta_p (oddGenerator 0) = 0 := by
  have hk0 : kappa 0 = 1 := by simp [kappa]
  rw [delta_p_oddGenerator_kappa_one hk0, delta_p_gen0_probe, mul_zero]

end TernaryPeriodPolynomials.Argument.ModFourBeta
