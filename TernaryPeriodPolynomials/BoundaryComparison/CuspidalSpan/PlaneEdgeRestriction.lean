module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.LocalInner
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.CuspReduction

@[expose] public section


/-!
# The identity-edge restriction of an `InnerBoundary` plane class (plane-side step 1)

Here we use the identity edge
`QuotientGroup.mk 1 : Edges`, whose `.plane`-endpoint is `cuspFlag .plane false`, the identity
cusp flag that `cuspRes n trivialCharacter .plane false` is built from
(`identityEdge_plane_eq`). Combined with `innerBoundary_iff_endpointStabilizerRestrictions`, an
`InnerBoundary` plane class's restriction to the identity edge's stabilizer vanishes
(`identityEdge_restriction_zero_of_innerBoundary`) — step 1 of the three-step plan for the
`InnerPlaneEdgeParabolic` input.
-/

noncomputable section

open GeneralEisenstein
open GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.Spectral.CuspOrbits

namespace TernaryPeriodPolynomials.Argument.CuspidalSpan


/-- The identity edge's `.plane`-endpoint is the identity-plane cusp flag. -/
theorem identityEdge_plane_eq :
    endpoint .plane (QuotientGroup.mk (1 : RationalGL3) : Edges) = cuspFlag .plane false := rfl

/-- If a `.plane`-side stratum class is `InnerBoundary`, its ambient `H2`-restriction to the
stabilizer of the identity edge vanishes. This is step 1 of the three-step plan for
`InnerPlaneEdgeParabolic`: the locally-inner statement at the binary-cusp flag, from which the
explicit edge-cocycle formula at `T` (step 2) and the coboundary identification (step 3) are to
be built. -/
theorem identityEdge_restriction_zero_of_innerBoundary {n : ℕ}
    {ξ : StratumH2 n trivialCharacter .plane} (inner : InnerBoundary n trivialCharacter .plane ξ) :
    endpointStabilizerRestriction n trivialCharacter .plane (QuotientGroup.mk (1 : RationalGL3))
      (cuspRes n trivialCharacter .plane false ξ) = 0 :=
  (innerBoundary_iff_endpointStabilizerRestrictions ξ).mp inner
    (QuotientGroup.mk (1 : RationalGL3))

end TernaryPeriodPolynomials.Argument.CuspidalSpan
