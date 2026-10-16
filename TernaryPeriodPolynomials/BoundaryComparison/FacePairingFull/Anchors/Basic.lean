module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairing.AssembleFromAnchor

@[expose] public section


/-!
# Face-pairing anchors

A `FacePairingAnchor b` for an inner line class `b` is a line representative `z₀` with an edge
primitive `w₀`, a plane representative `y₀` of some plane class that is edge-exact, and a nonzero
two-term `lineValue` sum. The positive-degree branch lemmas of `Proofs/FacePairing` build such an
anchor; it certifies both the non-exactness conclusion of `face_pairing_perfect`
(`AssembleFromAnchor.face_pairing_perfect_of_anchor`) and the non-vanishing of the trace pairing
(`TraceDetects.traceDetects_of_anchorData`).

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.BoundaryDuality.TraceRepresentatives
open TernaryPeriodPolynomials.BoundaryDuality.ChainLocal (lineValue)
open TernaryPeriodPolynomials.BoundaryDuality.L2Trace (traceDataL2)

namespace TernaryPeriodPolynomials.Argument.FacePairingFull

/-- **A face-pairing anchor for a line class `b`.** -/
def FacePairingAnchor {n : ℕ} (b : StratumH2 n trivialCharacter .line) : Prop :=
  ∃ (z₀ : MaximalCycles n trivialCharacter .line) (w₀ : EdgeCochains n trivialCharacter 1)
    (ξ : StratumH2 n trivialCharacter .plane) (y₀ : MaximalCycles n trivialCharacter .plane),
    classOf rationalLevel
      (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) z₀ = b ∧
    EdgePrimitive z₀ w₀ ∧
    classOf rationalLevel
      (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane) y₀ = ξ ∧
    PlaneEdgeExact y₀ ∧
    ∑ v : Fin 2, lineValue traceDataL2 (dualityData n trivialCharacter) v z₀ w₀ y₀ ≠ 0

end TernaryPeriodPolynomials.Argument.FacePairingFull
