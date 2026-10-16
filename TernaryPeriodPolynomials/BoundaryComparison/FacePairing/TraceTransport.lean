module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairing.NotBoundaryExactOfLineValueSum

@[expose] public section


/-!
# Transporting non-exactness from an anchor quadruple to any cohomologous one (M4/M5 bridge)

`TraceRepresentatives.trace_eq` gives representative-independence of the *trace* of the boundary
cup product: for any two quadruples `(z, w, y, γ)` and `(z₀, w₀, y₀, γ₀)`, each satisfying
`EdgePrimitive`/`VertexPrimitive`, with `z, z₀` cohomologous (`.line`), `y, y₀` cohomologous
(`.plane`), and the *second* representative `y₀` additionally `PlaneEdgeExact`, the traces of the
corresponding boundary cup products agree.

Combined with the sum formula (`ChainPairing.trace_eq_chainValue`, `ChainLocal.chainValue_eq_sum`)
and the generic non-exactness criterion (`TraceReduction.not_boundaryExact_of_trace`), this lets a
single self-constructed anchor quadruple `(z₀, w₀, y₀, γ₀)` — with `y₀` built so that
`PlaneEdgeExact y₀` holds (e.g. literally the `InnerBoundary` witness for the target plane class
`ξ`) and with a nonzero two-term `lineValue` sum at the anchor — certify non-exactness for *every*
quadruple `(z, w, y, γ)` cohomologous to the anchor and satisfying `EdgePrimitive`/
`VertexPrimitive`. In particular this covers the universally quantified `(z, w, y, γ)` in
`face_pairing_perfect` itself, whose own `w`/`γ` hypothesis clauses are literally
`EdgePrimitive`/`VertexPrimitive` (confirmed in `NotBoundaryExactOfLineValueSum`), so the anchor's
`lineValue` sum is the *only* thing that remains to compute.
-/

noncomputable section

open GeneralEisenstein
open GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.BoundaryDuality.TraceRepresentatives
open TernaryPeriodPolynomials.BoundaryDuality.TraceReduction
open TernaryPeriodPolynomials.BoundaryDuality.ChainPairing
open TernaryPeriodPolynomials.BoundaryDuality.ChainLocal (lineValue chainValue_eq_sum)
open TernaryPeriodPolynomials.BoundaryDuality.L2Trace (traceDataL2 isBoundaryTrace_traceDataL2)

namespace TernaryPeriodPolynomials.Argument.FacePairing


/-- **M4/M5 transport.** Non-exactness of the boundary cup product, established for one anchor
quadruple `(z₀, w₀, y₀, γ₀)` via a nonzero `lineValue` sum at the anchor, transports to *any*
quadruple `(z, w, y, γ)` satisfying `EdgePrimitive`/`VertexPrimitive` and cohomologous to the
anchor (`z` to `z₀` on the line side, `y` to `y₀` on the plane side), provided the anchor's plane
representative `y₀` is `PlaneEdgeExact`. -/
theorem not_boundaryExact_of_lineValue_sum_ne_zero_transport {n : ℕ}
    (z z₀ : MaximalCycles n trivialCharacter .line) (w w₀ : EdgeCochains n trivialCharacter 1)
    (y y₀ : MaximalCycles n trivialCharacter .plane)
    (γ γ₀ : (Fin 4 → RationalGL3) → Flags .line → ℂ)
    (hw : EdgePrimitive z w) (hγ : VertexPrimitive (dualityData n trivialCharacter) z y γ)
    (hw₀ : EdgePrimitive z₀ w₀) (hγ₀ : VertexPrimitive (dualityData n trivialCharacter) z₀ y₀ γ₀)
    (hz : classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) z =
      classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) z₀)
    (hy : classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane) y =
      classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane) y₀)
    (flat₀ : PlaneEdgeExact y₀)
    (hsum : ∑ v : Fin 2, lineValue traceDataL2 (dualityData n trivialCharacter) v z₀ w₀ y₀ ≠ 0) :
    ¬ BoundaryExact (boundaryValue (dualityData n trivialCharacter) w y γ) := by
  have htrace : traceDataL2.trace (boundaryValue (dualityData n trivialCharacter) w y γ) =
      traceDataL2.trace (boundaryValue (dualityData n trivialCharacter) w₀ y₀ γ₀) := by
    have h := trace_eq (dualityData n trivialCharacter) isBoundaryTrace_traceDataL2 hw hγ hw₀ hγ₀
      hz hy flat₀
    exact h
  have heq₀ : traceDataL2.trace (boundaryValue (dualityData n trivialCharacter) w₀ y₀ γ₀) =
      ∑ v : Fin 2, lineValue traceDataL2 (dualityData n trivialCharacter) v z₀ w₀ y₀ := by
    rw [trace_eq_chainValue traceDataL2 (dualityData n trivialCharacter) hγ₀]
    exact chainValue_eq_sum traceDataL2 (dualityData n trivialCharacter) z₀ w₀ y₀
  have hne : traceDataL2.trace (boundaryValue (dualityData n trivialCharacter) w y γ) ≠ 0 := by
    rw [htrace, heq₀]; exact hsum
  exact not_boundaryExact_of_trace isBoundaryTrace_traceDataL2 hne

end TernaryPeriodPolynomials.Argument.FacePairing
