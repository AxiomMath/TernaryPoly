module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.PairingCone
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.Model.CupP

@[expose] public section


/-!
# The face pairings are multiples of the evaluation on the corner chain of a given spanning cycle

`TraceEvaluation.traceComparison`, `PairingCone.traceValue_eq_evalOmega` and `ModelCupP.traceValueP_eq_evalOmega`
produce the evaluation chain `Ω` of the trace comparison without saying which cycle it comes from.  Here the
spanning cycle `v : coneR.X 4` is an input (`hspan` is the third component of `exists_fundamental_cycle`, for
`ω = mk v`), and the conclusions are stated for `Ω = cornerChain v`: `levelTrace_eq_evalCorner` for the level trace,
`traceValue_eq_evalCorner` for the line face pairing and `traceValueP_eq_evalCorner` for the plane face pairing.
In each, the value is `c` times the evaluation of the boundary cup product `boundaryValue` (`boundaryValueP`), and
also times the evaluation of the corner component of the cone cup product (`boundaryValue_eq_cone`).

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory Limits
open GeneralEisenstein GeneralEisenstein.Homogeneous TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.Argument.LevelTransfer
open TernaryPoly.SymmetricSpaceBoundaryGeometricCone
open TernaryPoly.SymmetricSpaceBoundaryMV (Flag)
open TernaryPeriodPolynomials.Argument.TopHomology
open TernaryPeriodPolynomials.BoundaryDuality.TraceRepresentatives
open TernaryPeriodPolynomials.Argument.FacePairing
open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison.ModelDiagonal
open TernaryPeriodPolynomials.Argument.FacePairingFull.Plane

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison

attribute [local instance] vertexAction

theorem levelTrace_eq_evalCorner (v : coneR.X 4)
    (hspan : ∀ (W : Type) [AddCommGroup W] [Module ℚ W] (c : coneR.X 4 ⟶ Rep.trivial ℚ Γ6 W),
      coneR.d 5 4 ≫ c = 0 →
      coinvHom (coneR.X 4) W c (Representation.Coinvariants.mk (coneR.X 4).ρ v) = 0 →
      ∃ η : coneR.X 3 ⟶ Rep.trivial ℚ Γ6 W, c = coneR.d 4 3 ≫ η) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ f : closedEdgeCochains rationalLevel,
      levelTrace f = c * evalOmega (cornerChain v) f.1 := by
  let ev : closedEdgeCochains rationalLevel →ₗ[ℂ] ℂ :=
    (evalOmega (cornerChain v)).comp (closedEdgeCochains rationalLevel).subtype
  have hexact : ∀ f : closedEdgeCochains rationalLevel, evalOmega (cornerChain v) f.1 = 0 →
      BoundaryExactAt rationalLevel f.1 := by
    intro f hf
    have hN6 : f.val ∈ closedEdgeCochains N6 := closedEdgeCochains_mono N6_le_rationalLevel f.2
    exact boundaryExactAt_of_N6 f.2 (boundaryExactAt_of_cornerChain v hspan ⟨f.val, hN6⟩ hf)
  have hker : ∀ f : closedEdgeCochains rationalLevel, ev f = 0 → levelTrace f = 0 :=
    fun f hf => levelTrace_eq_zero_of_boundaryExactAt (hexact f hf)
  obtain ⟨c, hc⟩ := exists_smul_of_ker_le levelTrace ev hker
  obtain ⟨f₀, hf₀⟩ := exists_closed_levelTrace_ne_zero
  refine ⟨c, ?_, hc⟩
  intro hc0
  apply hf₀
  rw [hc f₀, hc0, zero_mul]

/-- **The line face pairing is `c` times the evaluation on the corner chain of `v`.** -/
theorem traceValue_eq_evalCorner (v : coneR.X 4)
    (hspan : ∀ (W : Type) [AddCommGroup W] [Module ℚ W] (c : coneR.X 4 ⟶ Rep.trivial ℚ Γ6 W),
      coneR.d 5 4 ≫ c = 0 →
      coinvHom (coneR.X 4) W c (Representation.Coinvariants.mk (coneR.X 4).ρ v) = 0 →
      ∃ η : coneR.X 3 ⟶ Rep.trivial ℚ Γ6 W, c = coneR.d 4 3 ≫ η) :
    ∃ c : ℂ, c ≠ 0 ∧
      ∀ {n : ℕ} (z : MaximalCycles n trivialCharacter .line) (w : EdgeCochains n trivialCharacter 1)
        (y : MaximalCycles n trivialCharacter .plane) (s : EdgeCochains n trivialCharacter 1)
        (γ : (Fin 4 → RationalGL3) → Flags .line → ℂ)
        (_hw : EdgePrimitive z w) (_hγ : VertexPrimitive (dualityData n trivialCharacter) z y γ),
        traceValue z w y = c * evalOmega (cornerChain v)
            (boundaryValue (dualityData n trivialCharacter) w y γ) ∧
          traceValue z w y = c * evalOmega (cornerChain v)
            ((modelCup (dualityData n trivialCharacter) (a := 1) (b := 1) (m := 3) rfl
                (lineCone z.val.val w.val) (twistLine (dualityData n trivialCharacter) y.val.val s.val)).c -
              Ch.map (endRestr .line) γ) := by
  obtain ⟨c, hc, htr⟩ := levelTrace_eq_evalCorner v hspan
  refine ⟨c, hc, fun {n} z w y s γ hw hγ => ?_⟩
  have h1 : traceValue z w y = c * evalOmega (cornerChain v)
      (boundaryValue (dualityData n trivialCharacter) w y γ) := by
    rw [← trace_boundaryValue_eq_traceValue hγ]
    exact htr ⟨boundaryValue (dualityData n trivialCharacter) w y γ, boundaryValue_mem_closed _ hw hγ⟩
  refine ⟨h1, ?_⟩
  rw [← boundaryValue_eq_cone (dualityData n trivialCharacter) z.val.val w y s γ]
  exact h1

open TernaryPeriodPolynomials.Argument.FacePairingFull.Swap in
/-- **The plane face pairing is `c` times the evaluation on the corner chain of `v`.** -/
theorem traceValueP_eq_evalCorner (v : coneR.X 4)
    (hspan : ∀ (W : Type) [AddCommGroup W] [Module ℚ W] (c : coneR.X 4 ⟶ Rep.trivial ℚ Γ6 W),
      coneR.d 5 4 ≫ c = 0 →
      coinvHom (coneR.X 4) W c (Representation.Coinvariants.mk (coneR.X 4).ρ v) = 0 →
      ∃ η : coneR.X 3 ⟶ Rep.trivial ℚ Γ6 W, c = coneR.d 4 3 ≫ η) :
    ∃ c : ℂ, c ≠ 0 ∧
      ∀ {n : ℕ} (z : MaximalCycles n trivialCharacter .plane) (w : EdgeCochains n trivialCharacter 1)
        (y : MaximalCycles n trivialCharacter .line) (s : EdgeCochains n trivialCharacter 1)
        (γ : (Fin 4 → RationalGL3) → Flags .plane → ℂ)
        (_hw : EdgePrimitiveP z w) (_hγ : VertexPrimitiveP (dualityDataP n trivialCharacter) z y γ),
        traceValueP z w y = c * evalOmega (cornerChain v)
            (boundaryValueP (dualityDataP n trivialCharacter) w y γ) ∧
          traceValueP z w y = c * evalOmega (cornerChain v)
            ((modelCupP (dualityDataP n trivialCharacter) (a := 1) (b := 1) (m := 3) rfl
                (planeCone z.val.val w.val)
                (twistPlane (dualityDataP n trivialCharacter) y.val.val s.val)).c -
              Ch.map (endRestr .plane) γ) := by
  obtain ⟨c, hc, htr⟩ := levelTrace_eq_evalCorner v hspan
  refine ⟨c, hc, fun {n} z w y s γ hw hγ => ?_⟩
  have h1 : traceValueP z w y = c * evalOmega (cornerChain v)
      (boundaryValueP (dualityDataP n trivialCharacter) w y γ) := by
    rw [← trace_boundaryValue_eq_traceValueP hγ]
    exact htr ⟨boundaryValueP (dualityDataP n trivialCharacter) w y γ, boundaryValueP_mem_closed _ hw hγ⟩
  refine ⟨h1, ?_⟩
  rw [← boundaryValueP_eq_cone (dualityDataP n trivialCharacter) z.val.val w y s γ]
  exact h1

end TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
