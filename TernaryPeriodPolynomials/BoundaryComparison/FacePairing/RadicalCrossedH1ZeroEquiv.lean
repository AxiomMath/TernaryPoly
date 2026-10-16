module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairing.RadicalTrivialZero

@[expose] public section


/-!
# The degree-`0` radical crossed `H¹` is `HomogeneousPoly 0 × HomogeneousPoly 0`

Assembles `RadicalTrivialZero`'s two companion facts (`radicalCrossedBoundaries 0 = ⊥` and
`discreteRadicalCycles 0 = ⊤`) with the already degree-generic evaluation equivalence
`radicalCrossedEvaluationEquiv` into a genuine `LinearEquiv` `RadicalCrossedH1 0 ≃ₗ[ℂ]
HomogeneousPoly 0 × HomogeneousPoly 0`, with no exponential/Koszul machinery (that machinery is
intrinsically positive-degree-only).
-/

noncomputable section

open GeneralEisenstein Homogeneous Adelic Matrix MvPolynomial
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

namespace TernaryPeriodPolynomials.Argument.FacePairing


/-- The degree-`0` radical crossed cohomology is literally the cocycle space (its boundaries
vanish). -/
def radicalCrossedH1ZeroEquivCocycles :
    RadicalCrossedH1 0 ≃ₗ[ℂ] crossedCocycles (radicalRepresentation 0) :=
  Submodule.quotEquivOfEqBot _ radicalCrossedBoundaries_zero_eq_bot

/-- **The degree-`0` radical crossed `H¹` is `HomogeneousPoly 0 × HomogeneousPoly 0`.** -/
def radicalCrossedH1ZeroEquiv :
    RadicalCrossedH1 0 ≃ₗ[ℂ] HomogeneousPoly 0 × HomogeneousPoly 0 :=
  radicalCrossedH1ZeroEquivCocycles.trans
    ((radicalCrossedEvaluationEquiv 0).trans
      ((LinearEquiv.ofEq _ _ discreteRadicalCycles_zero_eq_top).trans Submodule.topEquiv))

end TernaryPeriodPolynomials.Argument.FacePairing
