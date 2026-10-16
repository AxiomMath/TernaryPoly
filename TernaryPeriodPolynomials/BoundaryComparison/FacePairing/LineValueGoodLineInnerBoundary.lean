module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairing.Good.LineFiberOfInnerBoundary
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairing.BridgeXInnerBoundary

@[expose] public section


/-!
# The good-line `lineValue` identity for an `InnerBoundary` line class, reduced to the plane-side
bridge (M4, good line, step 3)

Combines `GoodLineFiberOfInnerBoundary.exists_goodLineFiber_of_innerBoundary` (M4 step 1) and
`BridgeXInnerBoundary.bridgeX_mem_parabolicCocycles_of_innerBoundary` (M4 step 2) with the
library's `LocalPairingCaseL1Trivial.lineValue_goodLine_trivial_eq_bridge` to compute
`lineValue traceDataL2 ... 1 z w y` as an explicit `parabolicPairing` against `[bridgeX]` and
`[bridgeX']`, for the *specific* witnesses `z, w, ωU, θU, ...` produced by step 1. This reduces the
gap, for the good line, to exactly the plane-side membership
`hx'par : bridgeX' ... ∈ parabolicCocycles ...` — the Hecke-free analogue of M4 step 2 on the plane
side.

`hF` and `hxpar` are optional arguments (defaulted to the step-1/step-2 constructions); callers normally omit both and supply only `hx'par`.
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

namespace TernaryPeriodPolynomials.Argument.FacePairing


/-- **M4, good line, step 3.** For an `InnerBoundary` line coordinate witnessed by `z, w` and an
arbitrary plane class `y`, with the plane-side bridge membership `hx'par` supplied, `lineValue` is
an explicit nonzero multiple of a `parabolicPairing`. Composes `lineValue_goodLine_trivial_eq_bridge`
with `bridgeX_mem_parabolicCocycles_of_innerBoundary` (M4 step 2, Hecke-free): the gap for
the good line is exactly the plane-side membership `hx'par`. -/
theorem lineValue_goodLine_eq_of_innerBoundary {n : ℕ} (hn : 0 < n) (hodd : Odd n)
    {coordinate : StratumH2 n trivialCharacter .line}
    (inner : InnerBoundary n trivialCharacter .line coordinate)
    (z : MaximalCycles n trivialCharacter .line) (w : EdgeCochains n trivialCharacter 1)
    (hz : classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) z =
      coordinate)
    (hw : EdgePrimitive z w) (y : MaximalCycles n trivialCharacter .plane)
    (ωU θU : (Fin 2 → RationalGL3) → HomogeneousPoly n)
    (hωU : ∀ γ ∈ latL1.sub, ∀ a b,
      ωU ![γ * a, γ * b] = rationalCoefficientComponent n trivialCharacter γ (ωU ![a, b]))
    (hdωU : ∀ a b c, differentialOneRaw ωU ![a, b, c] = z.val.val ![a, b, c] L₁)
    (hθU : ∀ γ ∈ latL1.sub, ∀ a b,
      θU ![γ * a, γ * b] = rationalCoefficientComponent n trivialCharacter
        ((dualityData n trivialCharacter).φ γ) (θU ![a, b]))
    (hdθU : ∀ a b c, differentialOneRaw θU ![a, b, c] =
      y.val.val ![(dualityData n trivialCharacter).φ a, (dualityData n trivialCharacter).φ b,
        (dualityData n trivialCharacter).φ c] ((dualityData n trivialCharacter).dualFlag L₁))
    (hF : GoodLineFiber n trivialCharacter (levelStabilizer e₂) (lineCocycle z)
        (planeCocycle (dualityData n trivialCharacter) y) (edgeCochain w) ωU θU :=
      fiberHyp_goodLine (dualityData n trivialCharacter) z w y hw ωU hωU hdωU θU hθU hdθU)
    (hxpar : bridgeX hn 0 (phiTwist_trivial n) hF ∈
      parabolicCocycles (arithmeticBinaryRep (n + 1) 0) :=
      bridgeX_mem_parabolicCocycles_of_innerBoundary hn inner z hz hF)
    (hx'par : bridgeX' (-1) (psiTwist_trivial hodd) hF ∈
      parabolicCocycles (arithmeticBinaryRep (n + 1) (-1))) :
    lineValue traceDataL2 (dualityData n trivialCharacter) 1 z w y =
      -(-((n + 1).factorial : ℂ)) * parabolicPairing (twistedPairing_goodLine_trivial hodd)
        ⟨projectH1 (arithmeticBinaryRep (n + 1) 0) (bridgeX hn 0 (phiTwist_trivial n) hF),
          Submodule.mem_map_of_mem hxpar⟩
        ⟨projectH1 (arithmeticBinaryRep (n + 1) (-1))
          (bridgeX' (-1) (psiTwist_trivial hodd) hF), Submodule.mem_map_of_mem hx'par⟩ := by
  have h := lineValue_goodLine_trivial_eq_bridge hn hodd z w y hw ωU θU hωU hdωU hθU hdθU hF hxpar
    hx'par
  exact h

end TernaryPeriodPolynomials.Argument.FacePairing
