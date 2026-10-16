module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Cone.AssemblyEx
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.Face.Factorisation6Thm

@[expose] public section


/-!
# Proposition C.5 for every `Γ(N)`, `N ≥ 3`, `n ≥ 4`: unconditional

Formalized by Claude Sonnet 5.5.

`propC5_gammaN`: the uniform face factorisation `faceFactorisation6U` of the `Γ(6)` cone pairings (fibre integration: `m3Line` with `κ_L = -3`, S6, and `m3Plane` with `κ_P = +3`, S1, from `lineSum_final`,
`planeSum_final`, the flag geometry and the shuffle chains) feeds the `propC5_gammaN_of_faceFactorisation`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange

open TernaryPeriodPolynomials.Argument.GammaNFacesFull

/-- **Proposition C.5 (`ar:prop:graph`) for every `Γ(N)`, `N ≥ 3`, `n ≥ 4`.** -/
theorem propC5_gammaN {N n : ℕ} [NeZero N] (hN : 3 ≤ N) (hn : 4 ≤ n) : PropC5GammaN N n :=
  propC5_gammaN_of_faceFactorisation hN hn
    TernaryPeriodPolynomials.Argument.GammaNFaceFactor.faceFactorisation6U.toFF6

end TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange
