module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairing.LineValueBadLineInnerBoundary
public import TernaryPeriodPolynomials.BoundaryComparison.GoodPlaneSpan.EdgeParabolicAssembly
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Local.PairingCaseL0Odd

@[expose] public section


/-!
# The bad-line plane-side bridge membership `hx'par`, for an `InnerBoundary` plane class
(Hecke-free)

Bad-line analogue of `BridgeXPrimeInnerBoundary.bridgeX'_mem_parabolicCocycles_of_innerBoundary`
(good line). Supplies `LineValueBadLineInnerBoundary.lineValue_badLine_eq_of_innerBoundary`'s open
`hx'par` hypothesis — `badXOdd' hodd hF ∈ parabolicCrossed (levelRep (n + 1) (-1))` — unconditionally
from `InnerBoundary` at the plane, with no Hecke hypothesis.

The key new ingredient is `ParabolicDualityEdgeLevelThree.lean`'s `parabolicCrossedH1_eq (ρ) :
parabolicCrossedH1 ρ = TwoGenerator.parabolicH1 ρ (upper 1) (lower 1)` (namespace
`...ParabolicDuality.LevelThree`): it identifies the bad-line branch's own `parabolicCrossedH1
(levelRep (n + 1) (-1))` with exactly the predicate `GoodPlaneSpan.goodPlaneEdgeParabolic`
(already proved Hecke-free, needing only `InnerBoundary` at the plane) produces membership in.
Composing this identification with the library's own (already Hecke-free, declared before any
Hecke `variable` in scope) transport fact `LocalPairingCaseL0Odd.qcls_badXOdd'_eq` and
`LocalPairingCaseL0Odd.thetaH1_mem` reruns exactly the derivation
`LocalPairingCaseL0Odd.lineValue_eq_pairing_of_primitives` already performs inline (from a
caller-supplied `hyP`) to turn a good-plane-edge parabolic membership into a `badXOdd'`
membership — nothing new is proved mathematically, only the Hecke-eigenspace hypothesis that
inline derivation otherwise consumes is replaced by the unconditional
`GoodPlaneSpan.goodPlaneEdgeParabolic`.
-/

noncomputable section

open GeneralEisenstein Matrix
open GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.BoundaryDuality.TraceRepresentatives
open TernaryPeriodPolynomials.BoundaryDuality.TraceChains (levelStabilizer)
open TernaryPeriodPolynomials.BoundaryDuality.ChainLocal (lineValue)
open TernaryPeriodPolynomials.BoundaryDuality.L2Trace (traceDataL2)
open TernaryPeriodPolynomials.BoundaryDuality.L2Matrices (e₀ L₀ endpoint_line_e₀)
open TernaryPeriodPolynomials.BoundaryDuality.L2Assembly
open TernaryPeriodPolynomials.BoundaryDuality.FiberExact
open TernaryPeriodPolynomials.BoundaryDuality.FiberL0
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.IdentBad
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.LevelThree
  (parabolicCrossed parabolicCrossedH1 parabolicPairing twistedPairing_badLine_goodPlane
    parabolicCrossedH1_eq)
open TernaryPeriodPolynomials.BoundaryDuality.LocalPairingCaseL0Odd
  (qcls_badXOdd'_eq thetaH1_mem)
open TernaryPeriodPolynomials.BoundaryDuality.Kostant
  (badX badXOdd' levelThreeBridgeBadOdd)
open TernaryPeriodPolynomials.BoundaryDuality.FiberParabolicL0
  (lineValue_badLine_parabolicPairing)
open TernaryPeriodPolynomials.LevelThree.ParabolicBounds (levelRep)
open TernaryPeriodPolynomials.BoundaryDuality.StabilizerVanishing
  (topVanishing_levelStabilizer)
open TernaryPeriodPolynomials.LevelThree.BadLineLocal
open TernaryPeriodPolynomials.Argument.GoodPlaneSpan (goodPlaneEdgeParabolic)

namespace TernaryPeriodPolynomials.Argument.FacePairing


/-- **The bad-line plane-side bridge membership `hx'par`, for an `InnerBoundary` plane class
(Hecke-free).** For a bad-line fiber `hF` built from an `InnerBoundary` plane class `y`, the
dual-coordinate cocycle `badXOdd'` is parabolic. Supplies
`LineValueBadLineInnerBoundary.lineValue_badLine_eq_of_innerBoundary`'s open `hx'par` hypothesis
unconditionally. -/
theorem badXOdd'_mem_parabolicCrossed_of_innerBoundary {n : ℕ} (hn : 0 < n) (hodd : Odd n)
    (z : MaximalCycles n trivialCharacter .line) (w : EdgeCochains n trivialCharacter 1)
    (hw : EdgePrimitive z w) (y : MaximalCycles n trivialCharacter .plane)
    (ωU θU : (Fin 2 → RationalGL3) → HomogeneousPoly n)
    (hωU : ∀ γ ∈ latL0.sub, ∀ a b,
      ωU ![γ * a, γ * b] = rationalCoefficientComponent n trivialCharacter γ (ωU ![a, b]))
    (hdωU : ∀ a b c, differentialOneRaw ωU ![a, b, c] = z.val.val ![a, b, c] L₀)
    (hθU : ∀ γ ∈ latL0.sub, ∀ a b,
      θU ![γ * a, γ * b] = rationalCoefficientComponent n trivialCharacter
        ((dualityData n trivialCharacter).φ γ) (θU ![a, b]))
    (hdθU : ∀ a b c, differentialOneRaw θU ![a, b, c] =
      y.val.val ![(dualityData n trivialCharacter).φ a, (dualityData n trivialCharacter).φ b,
        (dualityData n trivialCharacter).φ c] ((dualityData n trivialCharacter).dualFlag L₀))
    (hinner : InnerBoundary n trivialCharacter .plane
      (classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane) y))
    (hF : BadLineFiber n (levelStabilizer e₀) (fun x => z.val.val x L₀)
        (fun x => y.val.val ![(dualityData n trivialCharacter).φ (x 0),
          (dualityData n trivialCharacter).φ (x 1), (dualityData n trivialCharacter).φ (x 2)]
          ((dualityData n trivialCharacter).dualFlag L₀))
        (fun x => w.val x e₀) ωU θU :=
      fiberHyp_line (dualityData n trivialCharacter) endpoint_line_e₀ latL0_le latL0_le_e₀
        z w y hw ωU hωU hdωU θU hθU hdθU) :
    badXOdd' hodd hF ∈ parabolicCrossed (levelRep (n + 1) (-1)) := by
  have hyP := goodPlaneEdgeParabolic n hn
    (classOf rationalLevel
      (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane) y) hinner
  rw [← parabolicCrossedH1_eq (levelRep (n + 1) (-1))] at hyP
  have hη' := hη_flag
    (η := fun x => y.val.val ![dualInvolution (x 0), dualInvolution (x 1), dualInvolution (x 2)]
      ((dualityData n trivialCharacter).dualFlag L₀)) y (fun _ => rfl)
  have hycls := qcls_badXOdd'_eq hodd hn hF y hη'
  exact mem_parabolicCrossed_of_qcls _ _
    (Eq.mp (congrArg (· ∈ parabolicCrossedH1 (levelRep (n + 1) (-1))) hycls.symm)
      (thetaH1_mem hodd hyP))

end TernaryPeriodPolynomials.Argument.FacePairing
