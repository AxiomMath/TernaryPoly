module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Anchors.Basic

@[expose] public section


/-!
# The face pairing as a trace: representative independence and detection

For a line cocycle `z` with edge primitive `w` and a plane cocycle `y`, the trace of the boundary
cup product `w ⌣ y^φ - γ` (for any vertex primitive `γ` of `z ⌣ y^φ`) is the scalar
`traceValue z w y = Σ_v lineValue v z w y` (`trace_eq_chainValue`, `chainValue_eq_sum`); it does
not involve `γ`. The trace of the boundary cup product is the well-defined value of the paper's
face pairing `⟨ , ⟩_Q`: it depends only on the classes of `z` and `y`
(`traceValue_eq_of_classes`), provided one plane representative is edge-exact, and it kills
exactly the boundary-exact cup products.

`traceDetects_of_anchorData` upgrades every anchor produced by the positive-degree branches
(`FacePairingAnchor`) from "the boundary cup product is not exact" (the statement of
`face_pairing_perfect`) to "the trace pairing is nonzero", for every choice of representatives.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.BoundaryDuality.TraceRepresentatives
open TernaryPeriodPolynomials.BoundaryDuality.TraceReduction
open TernaryPeriodPolynomials.BoundaryDuality.ChainPairing
open TernaryPeriodPolynomials.BoundaryDuality.ChainLocal (lineValue chainValue_eq_sum)
open TernaryPeriodPolynomials.BoundaryDuality.L2Trace
  (traceDataL2 isBoundaryTrace_traceDataL2)
open TernaryPeriodPolynomials.BoundaryDuality.StabilizerVanishing
  (lineCupExact)
open TernaryPeriodPolynomials.Argument.FacePairing

namespace TernaryPeriodPolynomials.Argument.FacePairingFull

/-- The value of the face pairing `⟨ , ⟩_Q` at a line cocycle `z` with edge primitive `w` and a
plane cocycle `y`: the sum over the two line cusps of the local values. -/
def traceValue {n : ℕ} (z : MaximalCycles n trivialCharacter .line)
    (w : EdgeCochains n trivialCharacter 1) (y : MaximalCycles n trivialCharacter .plane) : ℂ :=
  ∑ v : Fin 2, lineValue traceDataL2 (dualityData n trivialCharacter) v z w y

/-- The trace of the boundary cup product is `traceValue`, for any vertex primitive. -/
theorem trace_boundaryValue_eq_traceValue {n : ℕ} {z : MaximalCycles n trivialCharacter .line}
    {w : EdgeCochains n trivialCharacter 1} {y : MaximalCycles n trivialCharacter .plane}
    {γ : (Fin 4 → RationalGL3) → Flags .line → ℂ}
    (hγ : VertexPrimitive (dualityData n trivialCharacter) z y γ) :
    traceDataL2.trace (boundaryValue (dualityData n trivialCharacter) w y γ) =
      traceValue z w y := by
  rw [trace_eq_chainValue traceDataL2 (dualityData n trivialCharacter) hγ]
  exact chainValue_eq_sum traceDataL2 (dualityData n trivialCharacter) z w y

/-- **Representative independence of the face pairing.** If `z, z₀` are cohomologous, `y, y₀` are
cohomologous with `y₀` edge-exact, and `w, w₀` are edge primitives, the values agree. -/
theorem traceValue_eq_of_classes {n : ℕ}
    {z z₀ : MaximalCycles n trivialCharacter .line} {w w₀ : EdgeCochains n trivialCharacter 1}
    {y y₀ : MaximalCycles n trivialCharacter .plane}
    (hw : EdgePrimitive z w) (hw₀ : EdgePrimitive z₀ w₀)
    (hz : classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) z =
      classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) z₀)
    (hy : classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane) y =
      classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane) y₀)
    (flat₀ : PlaneEdgeExact y₀) :
    traceValue z w y = traceValue z₀ w₀ y₀ := by
  obtain ⟨γ, hγ⟩ := lineCupExact (dualityData n trivialCharacter) z y
  obtain ⟨γ₀, hγ₀⟩ := lineCupExact (dualityData n trivialCharacter) z₀ y₀
  rw [← trace_boundaryValue_eq_traceValue hγ, ← trace_boundaryValue_eq_traceValue hγ₀]
  exact trace_eq (dualityData n trivialCharacter) isBoundaryTrace_traceDataL2 hw hγ hw₀ hγ₀
    hz hy flat₀

/-- **Trace detection from an anchor.** An anchor for `b` yields a plane class `ξ` such that the
trace pairing of `b` with `ξ` is nonzero for every choice of representatives and primitives. -/
theorem traceDetects_of_anchorData {n : ℕ} {b : StratumH2 n trivialCharacter .line}
    (h : FacePairingAnchor b) :
    ∃ ξ : StratumH2 n trivialCharacter .plane, InnerBoundary n trivialCharacter .plane ξ ∧
      ∀ z : MaximalCycles n trivialCharacter .line,
        classOf rationalLevel
          (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) z = b →
      ∀ w : EdgeCochains n trivialCharacter 1, EdgePrimitive z w →
      ∀ y : MaximalCycles n trivialCharacter .plane,
        classOf rationalLevel
          (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane) y = ξ →
        traceValue z w y ≠ 0 := by
  obtain ⟨z₀, w₀, ξ, y₀, hz₀, hw₀, hy₀, hflat₀, hsum⟩ := h
  obtain ⟨s₀, hs₀⟩ := hflat₀
  refine ⟨ξ, ⟨y₀, hy₀, s₀, fun x e => hs₀ x e⟩, fun z hz w hw y hy => ?_⟩
  have hvalue := traceValue_eq_of_classes hw hw₀ (hz.trans hz₀.symm) (hy.trans hy₀.symm)
    ⟨s₀, hs₀⟩
  rw [hvalue]
  exact hsum

end TernaryPeriodPolynomials.Argument.FacePairingFull
