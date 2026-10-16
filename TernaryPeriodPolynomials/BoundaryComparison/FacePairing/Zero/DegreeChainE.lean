module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairing.Zero.DegreeChainD

@[expose] public section


/-!
# Degree-zero reconstruction, part E: `edgeK` at degree zero

Step 11 alone (`degree = 0` analogue of `edgeK`/`edgeK_injective`).
-/

noncomputable section

open GeneralEisenstein Matrix CategoryTheory
open GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Spectral.GoodLineHecke
open TernaryPeriodPolynomials.Spectral.GoodLineLocalOp
open TernaryPeriodPolynomials.Spectral.LocalUniqueness
open TernaryPeriodPolynomials.Spectral.ModularH2

namespace TernaryPeriodPolynomials.Argument.FacePairing


/-- **Step 11.** `degree = 0` analogue of `edgeK` (reusing the already-unconditional `KL 0`,
`toH2L 0`). -/
def edgeKZero : KL 0 →ₗ[ℂ] groupCohomology.H1 (arithmeticBinaryRep 1 0) :=
  goodLineBinaryEdgeZero.comp (LinearMap.codRestrict _ ((toH2L 0).comp (KL 0).subtype) (fun x => x.2))

theorem edgeKZero_injective : Function.Injective edgeKZero := by
  intro x y h
  have h1 := goodLineBinaryEdgeZero_injective h
  apply Subtype.ext
  exact toH2L_injective 0 (congrArg Subtype.val h1)

end TernaryPeriodPolynomials.Argument.FacePairing
