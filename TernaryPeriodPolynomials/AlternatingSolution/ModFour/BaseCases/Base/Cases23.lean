module

public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Base.Cases
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Base.Cases23Parts

@[expose] public section


/-! Base case (7,0): `beta_sym[7] = 0`, i.e. the `m = 0` column of the `W(j,m)` table
at `j = 7`. Computed the same way as `half_5_0` in `BaseCases22.lean`. -/

open MvPolynomial
open TernaryPoly.CharTwoNorm (a b c cplus d7 basis generator)

namespace TernaryPeriodPolynomials.Argument.ModFourBeta

set_option maxRecDepth 4000

theorem half_7_0 :
    threeTermNorm (baseSym 7 0) = C 2 *
      (g70_part1 + g70_part2 + g70_part3 + g70_part4 + g70_part5 + g70_part6 + g70_part7) := by





  simp [baseSym, mult, oddGenLiftSym, genLiftSym, basisLift, kappa, liftD7, liftCplus,
    liftC, liftB, liftA, threeTermNorm, g70_part1, g70_part2, g70_part3, g70_part4,
    g70_part5, g70_part6, g70_part7]
  ring

end TernaryPeriodPolynomials.Argument.ModFourBeta
