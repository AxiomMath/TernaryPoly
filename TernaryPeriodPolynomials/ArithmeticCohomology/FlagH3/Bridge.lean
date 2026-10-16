module

public import TernaryPeriodPolynomials.ArithmeticCohomology.FlagH3.FlagCoords
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Const.Uniform

@[expose] public section


/-!
# The classes `G_F` as the `H3FlagData` of the uniformity step

Formalized by Claude Sonnet 5.5.

`GammaNStokes.H3FlagData` (`ConstUniform`) asks for classes `G o ∈ H³(Stab o.out; ℚ)` spanning the cohomology of the flag groups.  `flagH3Data` provides them:
`G o = flagGen o.out`, the class on which the explicit bar-cycle functional `flagLam` takes the value `1`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FlagH3

open TernaryPeriodPolynomials.Argument.GammaNStokes
open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
open TernaryPoly.SymmetricSpaceBoundaryMV (Flag)
open TernaryPoly.BoundaryFaceResolutionComparison

/-- **Step (ii) of the face factorisation**: classes `G_F` spanning the (one-dimensional) `H³` of every flag group. -/
def flagH3Data : GammaNStokes.H3FlagData where
  G o := flagGen o.out
  span o y := ⟨flagLam o.out y, flagLam_eq_smul_flagGen o.out y⟩

theorem flagH3Data_G (o : labelOrbits Γ6 Flag) : flagH3Data.G o = flagGen o.out := rfl

/-- The evaluation functional on the class `G_o` is `1`. -/
theorem flagLam_flagH3Data_G (o : labelOrbits Γ6 Flag) : flagLam o.out (flagH3Data.G o) = 1 :=
  flagLam_flagGen o.out

end TernaryPeriodPolynomials.Argument.FlagH3
