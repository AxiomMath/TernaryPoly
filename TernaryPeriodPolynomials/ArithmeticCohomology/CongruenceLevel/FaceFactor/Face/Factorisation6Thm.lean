module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.M3LineFinal
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.M3PlaneFinal
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.Face.Factorisation6U

@[expose] public section


/-!
# `FaceFactorisation6U`

Formalized by Claude Sonnet 5.5.

The uniform factorisation of the `Γ(6)` cone pairings through the canonical pairing, from the fibre-integration identities for lines (`m3Line`) and planes (`m3Plane`).
-/

open TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNFaceFactor

theorem faceFactorisation6U : FaceFactorisation6U := faceFactorisation6U_of_M3At m3Line m3Plane

end TernaryPeriodPolynomials.Argument.GammaNFaceFactor
