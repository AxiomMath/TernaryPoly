module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.M3Cut
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.Flag.EvalInst
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.BLine5
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.BPlane4

@[expose] public section


/-!
# `FaceFactorisation6` from the fibre-integration identities for the cut primitive

Formalized by Claude Sonnet 5.5.

`faceFactorisation6_of_M3C_flagEval`: with the evaluation data `flagEval`, the default frames and the (B_L), (B_P) (`lineImageSumZero`, `planeImageSumZero`), `FaceFactorisation6` follows from
`M3LineC flagEval` and `M3PlaneC flagEval` alone.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNFaceFactor

open TernaryPeriodPolynomials.Argument.GammaNStokes
open TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange

theorem faceFactorisation6_of_M3C_flagEval (h3L : M3LineC flagEval) (h3P : M3PlaneC flagEval) : FaceFactorisation6 :=
  faceFactorisation6_of_M3C flagEval ConjFrames.default (lineImageSumZero ConjFrames.default)
    (planeImageSumZero ConjFrames.default) h3L h3P

end TernaryPeriodPolynomials.Argument.GammaNFaceFactor
