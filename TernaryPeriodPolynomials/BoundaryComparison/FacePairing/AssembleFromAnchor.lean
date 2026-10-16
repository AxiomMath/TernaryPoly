module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairing.TraceTransport
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.StabilizerVanishing

@[expose] public section


/-!
# Assembling `face_pairing_perfect` from a single anchor quadruple (M5 wiring)

Reduces the target `face_pairing_perfect` to exhibiting *one* anchor triple `(z₀, w₀, y₀)`
(cohomologous to the universally-quantified `(z, w, y)` the target itself supplies) with a
nonzero two-term `lineValue` sum. All the bookkeeping is generic, via
`TraceTransport.not_boundaryExact_of_lineValue_sum_ne_zero_transport`:

* `z₀, w₀` are supplied directly by the caller (typically unfolded straight from the line class
  `b`'s own `InnerBoundary` witness).
* `y₀` is supplied directly by the caller together with `hflat₀ : PlaneEdgeExact y₀`
  (typically unfolded straight from the plane class `ξ`'s own `InnerBoundary` witness — the same
  raw data proves both `PlaneEdgeExact y₀` and, repackaged, `InnerBoundary ... ξ` itself, since
  `differentialOne`'s `.val` field unfolds to exactly the `differentialOneRaw` formula; this file
  performs that repackaging for the conclusion's existential witness).
* `γ₀` is supplied *unconditionally*, for this specific `z₀, y₀`, by
  `StabilizerVanishing.lineCupExact` — no extra hypothesis needed.

So the only remaining mathematical content, after this file, is choosing `ξ` and an anchor
`(z₀, w₀, y₀)` cohomologous to it making the two-term `lineValue` sum nonzero — the "partner
construction".
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.BoundaryDuality.TraceRepresentatives
open TernaryPeriodPolynomials.BoundaryDuality.ChainLocal (lineValue)
open TernaryPeriodPolynomials.BoundaryDuality.L2Trace (traceDataL2)
open TernaryPeriodPolynomials.BoundaryDuality.StabilizerVanishing
  (lineCupExact)

namespace TernaryPeriodPolynomials.Argument.FacePairing


/-- **M5 wiring.** `face_pairing_perfect`'s conclusion for a line class `b`, given a line-side
anchor `(z₀, w₀)` representing `b` and `EdgePrimitive`, and a plane-side anchor `(y₀, ξ)`
representing a chosen plane class `ξ` with `y₀` `PlaneEdgeExact`, whose two-term `lineValue` sum
is nonzero. The vertex primitive `γ₀` at the anchor is supplied internally, unconditionally, by
`lineCupExact`. -/
theorem face_pairing_perfect_of_anchor {n : ℕ} {b : StratumH2 n trivialCharacter .line}
    (z₀ : MaximalCycles n trivialCharacter .line)
    (hz₀ : classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) z₀ = b)
    (w₀ : EdgeCochains n trivialCharacter 1) (hw₀ : EdgePrimitive z₀ w₀)
    {ξ : StratumH2 n trivialCharacter .plane}
    (y₀ : MaximalCycles n trivialCharacter .plane)
    (hy₀ : classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane) y₀ = ξ)
    (hflat₀ : PlaneEdgeExact y₀)
    (hsum : ∑ v : Fin 2, lineValue traceDataL2 (dualityData n trivialCharacter) v z₀ w₀ y₀ ≠ 0) :
    ∃ ξ' : StratumH2 n trivialCharacter .plane, InnerBoundary n trivialCharacter .plane ξ' ∧
      ∀ z : MaximalCycles n trivialCharacter .line,
        classOf rationalLevel
          (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) z = b →
      ∀ w : EdgeCochains n trivialCharacter 1,
        (∀ x e, z.val.val x (endpoint .line e) = differentialOneRaw w.val x e) →
      ∀ y : MaximalCycles n trivialCharacter .plane,
        classOf rationalLevel
          (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane) y = ξ' →
      ∀ γ : (Fin 4 → RationalGL3) → Flags .line → ℂ,
        γ ∈ cochains rationalLevel (functionRepresentation scalarTrivial (Flags .line)) 3 →
        (∀ x F, differentialThreeRaw γ x F =
          dualPairing n (z.val.val ![x 0, x 1, x 2] F)
            (y.val.val ![dualInvolution (x 2), dualInvolution (x 3), dualInvolution (x 4)]
              (dualFlag F))) →
        ¬ BoundaryExact (fun x e =>
          dualPairing n (w.val ![x 0, x 1] e)
            (y.val.val ![dualInvolution (x 1), dualInvolution (x 2), dualInvolution (x 3)]
              (dualFlag (endpoint .line e))) - γ x (endpoint .line e)) := by
  obtain ⟨s₀, hs₀⟩ := hflat₀
  obtain ⟨γ₀, hγ₀⟩ := lineCupExact (dualityData n trivialCharacter) z₀ y₀
  refine ⟨ξ, ⟨y₀, hy₀, s₀, fun x e => hs₀ x e⟩, fun z hz w hw y hy γ hγmem hγeq => ?_⟩
  have hw' : EdgePrimitive z w := hw
  have hγ' : VertexPrimitive (dualityData n trivialCharacter) z y γ := ⟨hγmem, hγeq⟩
  exact not_boundaryExact_of_lineValue_sum_ne_zero_transport z z₀ w w₀ y y₀ γ γ₀ hw' hγ' hw₀ hγ₀
    (hz.trans hz₀.symm) (hy.trans hy₀.symm) ⟨s₀, hs₀⟩ hsum

end TernaryPeriodPolynomials.Argument.FacePairing
