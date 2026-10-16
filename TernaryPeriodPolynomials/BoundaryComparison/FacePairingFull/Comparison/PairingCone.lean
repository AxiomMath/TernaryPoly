module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.Model.Cup
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.TraceEvaluation
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.TraceDetects

@[expose] public section


/-!
# The face pairing is a multiple of the evaluation on the fundamental cycle of the cone cup product

Combination of the whole-boundary trace comparison `TraceEvaluation.traceComparison` (the boundary trace is a nonzero
multiple of the evaluation `evalOmega Ω` on a cycle `Ω` of the model cone, tied to the boundary fundamental class) with
`ModelCup.modelCup_eq` (the corner cochain of the model's face pairing represents the cone cup product of the
line-supported cone cocycles `(z, 0, w)` and `(y^φ, 0, s^φ)`).

`traceValue_eq_evalOmega`: for admissible data (a line cocycle `z` with edge primitive `w`, a plane cocycle `y` with edge
primitive `s`, a vertex primitive `γ`), the face pairing value `traceValue z w y` of the paper's `⟨ , ⟩_Q` is the
constant `c ≠ 0` of the trace comparison times `evalOmega Ω` of the corner cochain `(modelCup U U').c - rₗ γ` of
the cone cup product `U ⌣ U'`.  The identification of `evalOmega Ω` on such a cone cup with the geometric Poincaré
pairing on `∂M` (`GeoPairing`) is the compatibility of the model cap with the library's cap, not asserted here.

Formalized by Claude Sonnet 5.5.
-/

open GeneralEisenstein GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.BoundaryDuality.TraceRepresentatives
open TernaryPeriodPolynomials.Argument.FacePairing
open TernaryPoly.SymmetricSpaceBoundaryMV (Flag)
open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison.ModelDiagonal

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison

/-- **The face pairing is `c` times the evaluation on `Ω` of the corner cochain of the cone cup product.** -/
theorem traceValue_eq_evalOmega :
    ∃ (Ω : MonoidAlgebra ℚ ((Fin 4 → RationalGL3) × Flag)) (c : ℂ), c ≠ 0 ∧
      ∀ {n : ℕ} (z : MaximalCycles n trivialCharacter .line) (w : EdgeCochains n trivialCharacter 1)
        (y : MaximalCycles n trivialCharacter .plane) (s : EdgeCochains n trivialCharacter 1)
        (γ : (Fin 4 → RationalGL3) → Flags .line → ℂ)
        (_hw : EdgePrimitive z w) (_hγ : VertexPrimitive (dualityData n trivialCharacter) z y γ),
        traceValue z w y = c * evalOmega Ω
          ((modelCup (dualityData n trivialCharacter) (a := 1) (b := 1) (m := 3) rfl
              (lineCone z.val.val w.val) (twistLine (dualityData n trivialCharacter) y.val.val s.val)).c -
            Ch.map (endRestr .line) γ) := by
  obtain ⟨Ω, c, κ, hc, hκ, htr, -, -⟩ := traceComparison
  refine ⟨Ω, c, hc, fun {n} z w y s γ hw hγ => ?_⟩
  rw [← boundaryValue_eq_cone (dualityData n trivialCharacter) z.val.val w y s γ,
    ← trace_boundaryValue_eq_traceValue hγ]
  exact htr ⟨boundaryValue (dualityData n trivialCharacter) w y γ, boundaryValue_mem_closed _ hw hγ⟩

end TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
