module

public import TernaryPeriodPolynomials.BoundaryComparison.Stokes.C5
public import TernaryPeriodPolynomials.ArithmeticCohomology.FaceDescent.DescentPerfect

@[expose] public section


/-!
# Proposition C.5 by the paper's route, and the descended face pairing

Formalized by Claude Sonnet 5.5.

* `propC5_gammaN_paperRoute`: Proposition C.5 for every `Γ(N)`, `N ≥ 3`, `n ≥ 4`, from the paper's four inputs at the common level `lcm(N, 6)` (Eisenstein existence, dual series, perfect canonical line pairings, and the literal Stokes lemma
  `stokes_gammaN_literal_uncond`) through `GammaNC5FaceObligations`; no abstract obligation remains.  `stokesAtLevel_of_literal` is the new link (the Stokes field from `StokesGammaNLiteral`), `propC5_gammaN_printed_paperRoute` the printed-`T` form.
* `descended_isPerfPair`, `lineFace_descended_isPerfPair`, `planeFace_descended_isPerfPair` (and the `_En` forms for `E_n`): on the invariants of the finite covering group (determinant and reflection elements included) the canonical face pairing is a perfect pairing
  (`LinearMap.IsPerfPair`), assembled from the `cusp_descends_left/right`.
-/

namespace TernaryPeriodPolynomials.Argument.Statements.PropC5PaperRoute

alias stokesAtLevel_of_literal :=
  TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange.stokesAtLevel_of_literal
alias propC5_gammaN_paperRoute :=
  TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange.propC5_gammaN_paperRoute
alias propC5_gammaN_printed_paperRoute :=
  TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange.propC5_gammaN_printed_paperRoute
alias descended_isPerfPair := TernaryPeriodPolynomials.Argument.FaceDescent.FaceAction.descended_isPerfPair
alias lineFace_descended_isPerfPair :=
  TernaryPeriodPolynomials.Argument.FaceDescent.lineFace_descended_isPerfPair
alias planeFace_descended_isPerfPair :=
  TernaryPeriodPolynomials.Argument.FaceDescent.planeFace_descended_isPerfPair
alias lineFace_descended_isPerfPair_En :=
  TernaryPeriodPolynomials.Argument.FaceDescent.lineFace_descended_isPerfPair_En
alias planeFace_descended_isPerfPair_En :=
  TernaryPeriodPolynomials.Argument.FaceDescent.planeFace_descended_isPerfPair_En

end TernaryPeriodPolynomials.Argument.Statements.PropC5PaperRoute
