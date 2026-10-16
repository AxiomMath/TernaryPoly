module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairing.LineValueGoodLineInnerBoundary

@[expose] public section


/-!
# From a nonzero `lineValue` sum to non-exactness of the boundary cup product (M4, generic step)

Composes the trace-chain-value bridge (`ChainPairing.trace_eq_chainValue`), its localization to
line cusps (`ChainLocal.chainValue_eq_sum`), and the generic non-exactness criterion
(`TraceReduction.not_boundaryExact_of_trace`) with the boundary trace of the level
(`L2Trace.isBoundaryTrace_traceDataL2`): for *any* `z, w, y, γ` with `γ` a vertex primitive of the
twisted cup product (`VertexPrimitive`, matching the target's own `γ` hypothesis verbatim, since
`(dualityData n χ).B = dualPairing n`, `.φ = dualInvolution`, `.dualFlag = dualFlag` by
definition), the boundary cup product `boundaryValue w y γ` is non-exact as soon as the two-term
sum of `lineValue` over the line cusps `v : Fin 2` is nonzero. This isolates the remaining content
of the target to a scalar nonvanishing statement, independent of `boundarySummand`/Hecke sourcing.
-/

noncomputable section

open GeneralEisenstein
open TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.BoundaryDuality.TraceRepresentatives
open TernaryPeriodPolynomials.BoundaryDuality.TraceReduction
open TernaryPeriodPolynomials.BoundaryDuality.ChainPairing
open TernaryPeriodPolynomials.BoundaryDuality.ChainLocal (lineValue chainValue_eq_sum)
open TernaryPeriodPolynomials.BoundaryDuality.L2Trace (traceDataL2 isBoundaryTrace_traceDataL2)

namespace TernaryPeriodPolynomials.Argument.FacePairing


/-- **M4, generic reduction.** For a vertex primitive `γ` of the twisted cup product of `z` and
`y`, the boundary cup product is non-exact as soon as the sum of `lineValue` over the two line
cusps is nonzero. Independent of `boundarySummand`/Hecke sourcing: `z, w, y` are arbitrary. -/
theorem not_boundaryExact_of_lineValue_sum_ne_zero {n : ℕ}
    (z : MaximalCycles n trivialCharacter .line) (w : EdgeCochains n trivialCharacter 1)
    (y : MaximalCycles n trivialCharacter .plane)
    (γ : (Fin 4 → RationalGL3) → Flags .line → ℂ)
    (hγ : VertexPrimitive (dualityData n trivialCharacter) z y γ)
    (hsum : ∑ v : Fin 2, lineValue traceDataL2 (dualityData n trivialCharacter) v z w y ≠ 0) :
    ¬ BoundaryExact (boundaryValue (dualityData n trivialCharacter) w y γ) := by
  have heq : traceDataL2.trace (boundaryValue (dualityData n trivialCharacter) w y γ) =
      ∑ v : Fin 2, lineValue traceDataL2 (dualityData n trivialCharacter) v z w y := by
    rw [trace_eq_chainValue traceDataL2 (dualityData n trivialCharacter) hγ]
    exact chainValue_eq_sum traceDataL2 (dualityData n trivialCharacter) z w y
  have hne : traceDataL2.trace (boundaryValue (dualityData n trivialCharacter) w y γ) ≠ 0 := by
    rw [heq]; exact hsum
  exact not_boundaryExact_of_trace isBoundaryTrace_traceDataL2 hne

end TernaryPeriodPolynomials.Argument.FacePairing
