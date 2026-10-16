module

public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Base.Cases
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Base.Cases22Parts

@[expose] public section


/-! Base case (5,0): `beta_sym[5] = 0`, i.e. the `m = 0` column of the `W(j,m)` table at
`j = 5`. Computed the same way as `half_1_0`/`reduceTwo_g10`/`pi_1_0`/`case_1_0` in
`BaseCases.lean`. -/

open MvPolynomial
open TernaryPoly.CharTwoNorm (a b c cplus d7 basis generator)

namespace TernaryPeriodPolynomials.Argument.ModFourBeta

set_option maxRecDepth 4000

theorem half_5_0 :
    threeTermNorm (baseSym 5 0) = C 2 *
      (g50_part1 + g50_part2 + g50_part3 + g50_part4 + g50_part5) := by
  simp [baseSym, mult, oddGenLiftSym, genLiftSym, basisLift, kappa, liftD7, liftCplus, liftC,
    liftB, liftA, threeTermNorm, g50_part1, g50_part2, g50_part3, g50_part4, g50_part5]
  ring

end TernaryPeriodPolynomials.Argument.ModFourBeta
