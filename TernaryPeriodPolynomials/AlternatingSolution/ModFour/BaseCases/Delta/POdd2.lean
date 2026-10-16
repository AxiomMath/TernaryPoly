module

public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Delta.KappaOneReduction
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Delta.PGen2

@[expose] public section


/-!
`delta_p (oddGenerator 2) = 0`, by the kappa-one-lift composition: lift the generator-level fact `delta_p_gen2_probe` through `delta_p_oddGenerator_kappa_one`
(valid since `kappa 2 = 1`); the extra `d7` factor multiplies through a zero
right-hand side, so no `ring` normalization against a large explicit polynomial is
needed.
-/

open MvPolynomial TernaryPoly.CharTwoNorm

namespace TernaryPeriodPolynomials.Argument.ModFourBeta

theorem delta_p_odd2_eq_probe : delta_p (oddGenerator 2) = 0 := by
  have hk2 : kappa 2 = 1 := by simp [kappa]
  rw [delta_p_oddGenerator_kappa_one hk2, delta_p_gen2_probe, mul_zero]

end TernaryPeriodPolynomials.Argument.ModFourBeta
