module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairing.Good.LineFiberOfInnerBoundary
public import TernaryPeriodPolynomials.BoundaryComparison.CuspidalSpan.Defs
public import TernaryPeriodPolynomials.BoundaryComparison.CuspidalSpan.InnerPlaneEdgeParabolicProof
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Parabolic.DualityIdentPlane

@[expose] public section


/-!
# `bridgeX'` is parabolic for an `InnerBoundary` plane class (Hecke-free)

Hecke-free analogue of `ParabolicDualityIdentPlane.bridgeX'_mem_parabolicCocycles_trivial`:
replaces its "known joint Hecke-eigenclass with bounded `T₂`-eigenvalue" hypothesis `hx` by the
structurally different `VanishesOnGood`/`InnerBoundary` hypotheses on the plane class itself, via
`CuspidalSpan.InnerPlaneEdgeParabolicProof.innerPlaneEdgeParabolic_proof` ("Input 1" of the
bad-plane cuspidal span, proved unconditionally there — see `Revision/Proofs/CuspidalSpan/OddCase
.lean`'s docstring for `InnerPlaneEdgeParabolic`, which explicitly anticipates exactly this
substitution).

This supplies `LineValueGoodLineInnerBoundary.lineValue_goodLine_eq_of_innerBoundary`'s own
`hx'par` argument (M4, good line, step 3's gap).
-/

noncomputable section

open GeneralEisenstein Matrix
open GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.GoodBuildingPaths.Helpers
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.Spectral.LineCoordinates
open TernaryPeriodPolynomials.Spectral.IdentityPlaneCoordinate
open TernaryPeriodPolynomials.Spectral.GoodLineHecke
open TernaryPeriodPolynomials.Spectral.GoodLineLocalOp
open TernaryPeriodPolynomials.Spectral.LocalUniqueness
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.BoundaryDuality.TraceChains (levelStabilizer)
open TernaryPeriodPolynomials.BoundaryDuality.ChainLocal (lineValue)
open TernaryPeriodPolynomials.BoundaryDuality.L2Trace (traceDataL2)
open TernaryPeriodPolynomials.BoundaryDuality.L2Matrices (e₂ L₁)
open TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.BoundaryDuality.TraceRepresentatives
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.LevelOne
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.Ident
open TernaryPeriodPolynomials.BoundaryDuality.FiberExact
open TernaryPeriodPolynomials.BoundaryDuality.FiberL1
open TernaryPeriodPolynomials.BoundaryDuality.HeckeAdjointMembershipGood
open TernaryPeriodPolynomials.BoundaryDuality.L2Assembly
open TernaryPeriodPolynomials.BoundaryDuality.LocalPairingCaseL1Trivial
open TernaryPeriodPolynomials.BoundaryDuality.Kostant
  (bridgeX bridgeX' phiTwist_trivial psiTwist_trivial)
open TernaryPeriodPolynomials.Argument.CuspidalSpan

namespace TernaryPeriodPolynomials.Argument.FacePairing


variable {n : ℕ} {Λe : Subgroup RationalGL3} {ζ η : (Fin 3 → RationalGL3) → HomogeneousPoly n}
  {ω ωU θU : (Fin 2 → RationalGL3) → HomogeneousPoly n}

/-- **M4, good line, step 2 (Hecke-free).** `bridgeX'` is a parabolic cocycle whenever the Shapiro
coordinate of the plane class at the base plane is an `InnerBoundary` class vanishing at the good
planes — no Hecke hypothesis needed. Hecke-free analogue of
`ParabolicDualityIdentPlane.bridgeX'_mem_parabolicCocycles_trivial`, substituting its Hecke
hypothesis `hx` by `hgood`/`hinner` via `innerPlaneEdgeParabolic_proof`. -/
theorem bridgeX'_mem_parabolicCocycles_of_innerBoundary (hn : 0 < n) (hodd : Odd n)
    (y : cocycles rationalLevel
      (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane))
    (hgood : VanishesOnGood n trivialCharacter .plane
      (classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane) y))
    (hinner : InnerBoundary n trivialCharacter .plane
      (classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane) y))
    (hF : GoodLineFiber n trivialCharacter Λe ζ η ω ωU θU)
    (hη : ∀ x, η x = y.val.val ![dualInvolution (x 0), dualInvolution (x 1),
      dualInvolution (x 2)] ((dualityData n trivialCharacter).dualFlag L₁)) :
    bridgeX' (-1) (psiTwist_trivial hodd) hF ∈
      parabolicCocycles (arithmeticBinaryRep (n + 1) (-1)) := by
  have hη' := eta_eq_cocycleAtPlane n trivialCharacter y hη
  have hpar := innerPlaneEdgeParabolic_proof hn hodd
    (classOf rationalLevel
      (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane) y)
    hgood hinner
  rw [cuspRes_plane_false_classOf] at hpar
  have hFpar : identityPlaneBinaryEdgeCycle n
      (relOfP hF (cocycleAtPlane n trivialCharacter y) hη') ∈
      parabolicCocycles (arithmeticBinaryRep (n + 1) (-1)) := by
    apply mem_parabolicCocycles_of_projectH1_mem
    rw [projectH1_edgeCycle_eq_edgeH2 hn hodd hF _ hη']
    exact hpar
  exact swapPullback_mem_parabolicCocycles hodd (-1) hFpar
    (fun γ => bridgeX'_apply_trivial hodd hF _ hη' γ)

end TernaryPeriodPolynomials.Argument.FacePairing
