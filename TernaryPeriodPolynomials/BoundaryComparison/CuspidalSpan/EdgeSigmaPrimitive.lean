module

public import TernaryPeriodPolynomials.BoundaryComparison.CuspidalSpan.PlaneEdgeRestriction
public import TernaryPeriodPolynomials.BoundaryComparison.CuspidalSpan.EdgeStabilizerMembership
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.Identity.PlaneCoordinate

@[expose] public section


/-!
# A `Σ₀`-level ad hoc primitive from an `InnerBoundary` plane class (plane-side step 2a)

Mirrors the bridge technique of `Argument.FacePairing.KLMembership`, but stops at the ad hoc coboundary witness
instead of continuing to Mathlib-level `H2`-vanishing: for `ξ` with an `InnerBoundary` witness, we
produce an explicit ambient cocycle `C₀ : cocycles Λ₀ (ρn n)` representing
`cuspRes n trivialCharacter .plane false ξ`, together with an ad hoc primitive on
`Σ₀ := fixedPointLevel rationalLevel standardBadEdge` whose `boundaryMap` matches `C₀`'s
restriction to `Σ₀`. This is step 2a of the plan for `InnerPlaneEdgeParabolic`.
-/

noncomputable section

open GeneralEisenstein
open GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.Spectral.CuspOrbits
open TernaryPeriodPolynomials.Spectral.PlaneCoordinates
open TernaryPeriodPolynomials.Spectral.IdentityPlaneCoordinate
open TernaryPeriodPolynomials.SphericalDetection.Helpers

namespace TernaryPeriodPolynomials.Argument.CuspidalSpan


/-- Step 2a: an `InnerBoundary` plane class has an ambient cocycle representative `C₀` on `Λ₀`
whose restriction to `Σ₀` is an ad hoc coboundary. -/
theorem sigmaPrimitive_of_innerBoundary {n : ℕ} {ξ : StratumH2 n trivialCharacter .plane}
    (inner : InnerBoundary n trivialCharacter .plane ξ) :
    ∃ C₀ : cocycles Λ₀ (ρn n), classOf Λ₀ (ρn n) C₀ = cuspRes n trivialCharacter .plane false ξ ∧
      ∃ primitive : cochains (fixedPointLevel rationalLevel standardBadEdge) (ρn n) 1,
        boundaryMap (fixedPointLevel rationalLevel standardBadEdge) (ρn n) primitive =
          subgroupRestrictionCycle
            (fixedPointLevel_edge_le_endpoint .plane (QuotientGroup.mk (1 : RationalGL3)))
            (ρn n) C₀ := by
  have restriction := identityEdge_restriction_zero_of_innerBoundary inner
  revert restriction
  refine Quotient.inductionOn' (cuspRes n trivialCharacter .plane false ξ)
    (fun C₀ restriction => ?_)
  refine ⟨C₀, rfl, ?_⟩
  have restriction2 :
      classOf (fixedPointLevel rationalLevel standardBadEdge) (ρn n)
        (subgroupRestrictionCycle
          (fixedPointLevel_edge_le_endpoint .plane (QuotientGroup.mk (1 : RationalGL3)))
          (ρn n) C₀) = 0 := restriction
  obtain ⟨primitive, hprimitive⟩ := (classOf_eq_zero_iff _ _ _).mp restriction2
  exact ⟨primitive, Subtype.ext hprimitive⟩

end TernaryPeriodPolynomials.Argument.CuspidalSpan
