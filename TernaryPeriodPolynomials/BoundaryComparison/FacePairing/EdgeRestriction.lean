module

public import TernaryPeriodPolynomials.Building.GoodPaths.Helpers
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Good.Line
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.StabilizerRestriction
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.LocalInner

@[expose] public section


/-!
# The `baseEdge` complete-flag restriction of an `InnerBoundary` class (M1a, step 1)

`baseEdge` (`GoodBuildingPaths.Helpers`) is the complete-flag edge whose line-side endpoint is the
good line `rationalGoodLine` (`baseEdge_line_eq_goodLine`). For a `.line`-side stratum class that
is `InnerBoundary`, `innerBoundary_iff_endpointStabilizerRestrictions` gives vanishing of its
restriction to the stabilizer of *every* complete flag; specialising to `baseEdge` gives the
locally-inner statement at the good-line flag needed for the Hecke-free trace argument: `baseEdge_restriction_zero_of_innerBoundary`.

Convert to the `rationalGoodLine` form downstream, locally, via
`baseEdge_line_eq_goodLine`, rather than inside a fresh statement's signature.
-/

noncomputable section

open GeneralEisenstein
open GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.GoodBuildingPaths.Helpers
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

namespace TernaryPeriodPolynomials.Argument.FacePairing


/-- The good-line edge class `baseEdge`'s line-side endpoint is the good line itself. -/
theorem baseEdge_line_eq_goodLine :
    endpoint .line (QuotientGroup.mk baseEdge : Edges) = QuotientGroup.mk rationalGoodLine := by
  apply line_eq_of_column_eq
  intro index
  rw [baseEdge_column]
  fin_cases index <;> simp

/-- If a `.line`-side stratum class is `InnerBoundary`, its ambient `H2`-restriction to the
stabilizer of the `baseEdge` complete flag vanishes. This is step 1 of the three-step plan for
M1a option (A3): the locally-inner statement at the binary-cusp flag, from which the explicit
edge-cocycle formula at `T` (step 2) and the coboundary identification (step 3) are to be built. -/
theorem baseEdge_restriction_zero_of_innerBoundary {degree : ℕ} {character : RankOneCharacter}
    {coordinate : StratumH2 degree character .line}
    (inner : InnerBoundary degree character .line coordinate) :
    endpointStabilizerRestriction degree character .line (QuotientGroup.mk baseEdge)
      (fixedPointH2 rationalLevel (rationalCoefficientComponent degree character)
        (endpoint .line (QuotientGroup.mk baseEdge : Edges)) coordinate) = 0 :=
  (innerBoundary_iff_endpointStabilizerRestrictions coordinate).mp inner
    (QuotientGroup.mk baseEdge)

end TernaryPeriodPolynomials.Argument.FacePairing
