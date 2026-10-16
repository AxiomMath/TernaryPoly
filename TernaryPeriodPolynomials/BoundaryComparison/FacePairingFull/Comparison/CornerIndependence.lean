module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.PairingCone
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.Model.CupP

@[expose] public section


/-!
# The cone cup pairing does not see the corner ambiguity of the lifts

An inner line class `[z]` lifts to the cone cocycle `(z, 0, w)` for an edge primitive `w` of `z`, and an inner plane class `[y]`
to the `φ`-transported cone cocycle `(y^φ, 0, s^φ)`; the edge primitives are determined only up to a corner cocycle
(`InnerLiftAmbiguity`: two lifts differ by `cornerClass e`, which restricts to zero on both faces).  On the cone cup
product of the two lifts, the evaluation `evalOmega Ω` on the fundamental cycle of the corner cochain
`(modelCup U U').c - rₗ γ` (which is `c⁻¹` times the face pairing, `PairingCone.traceValue_eq_evalOmega`) does not depend on
the edge primitives `w`, `s`: two edge primitives `w, w'` of the same line cocycle give the same value
(`cone_pairing_corner_independent`); the same for the plane-supported twin (`cone_pairingP_corner_independent`).
Equivalently the corner cochain `(w' - w) ⌣ y^φ` of the difference of the two cone cup products evaluates to zero on `Ω`
(`corner_difference_evalOmega_zero`).

Formalized by Claude Sonnet 5.5.
-/

open GeneralEisenstein GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.BoundaryDuality.TraceRepresentatives
open TernaryPeriodPolynomials.Argument.FacePairing
open TernaryPeriodPolynomials.Argument.FacePairingFull.Plane
open TernaryPoly.SymmetricSpaceBoundaryMV (Flag)
open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison.ModelDiagonal

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison

/-- **Corner-ambiguity independence of the cone cup pairing (line side).**  For an inner plane cocycle `y` (it has an edge
primitive) and a line cocycle `z`, the evaluation on `Ω` of the corner cochain of the cone cup product of the lifts
`(z, 0, w)` and `(y^φ, 0, s^φ)` is the same for all edge primitives `w` of `z` and all `s`. -/
theorem cone_pairing_corner_independent :
    ∃ (Ω : MonoidAlgebra ℚ ((Fin 4 → RationalGL3) × Flag)) (c : ℂ), c ≠ 0 ∧
      ∀ {n : ℕ} (z : MaximalCycles n trivialCharacter .line) (w w' : EdgeCochains n trivialCharacter 1)
        (y : MaximalCycles n trivialCharacter .plane) (s s' : EdgeCochains n trivialCharacter 1)
        (γ : (Fin 4 → RationalGL3) → Flags .line → ℂ)
        (_hw : EdgePrimitive z w) (_hw' : EdgePrimitive z w') (_hy : PlaneEdgeExact y)
        (_hγ : VertexPrimitive (dualityData n trivialCharacter) z y γ),
        evalOmega Ω
          ((modelCup (dualityData n trivialCharacter) (a := 1) (b := 1) (m := 3) rfl
              (lineCone z.val.val w'.val) (twistLine (dualityData n trivialCharacter) y.val.val s'.val)).c -
            Ch.map (endRestr .line) γ) =
        evalOmega Ω
          ((modelCup (dualityData n trivialCharacter) (a := 1) (b := 1) (m := 3) rfl
              (lineCone z.val.val w.val) (twistLine (dualityData n trivialCharacter) y.val.val s.val)).c -
            Ch.map (endRestr .line) γ) := by
  obtain ⟨Ω, c, hc, H⟩ := traceValue_eq_evalOmega
  refine ⟨Ω, c, hc, fun {n} z w w' y s s' γ hw hw' hy hγ => ?_⟩
  have h1 := H z w' y s' γ hw' hγ
  have h2 := H z w y s γ hw hγ
  have h3 : traceValue z w' y = traceValue z w y :=
    traceValue_eq_of_classes hw' hw rfl rfl hy
  rw [h1] at h3
  rw [h2] at h3
  exact mul_left_cancel₀ hc h3

/-- **The same for the plane-supported twin** (`⟨ , ⟩_P`). -/
theorem cone_pairingP_corner_independent :
    ∃ (Ω : MonoidAlgebra ℚ ((Fin 4 → RationalGL3) × Flag)) (c : ℂ), c ≠ 0 ∧
      ∀ {n : ℕ} (z : MaximalCycles n trivialCharacter .plane) (w w' : EdgeCochains n trivialCharacter 1)
        (y : MaximalCycles n trivialCharacter .line) (s s' : EdgeCochains n trivialCharacter 1)
        (γ : (Fin 4 → RationalGL3) → Flags .plane → ℂ)
        (_hw : EdgePrimitiveP z w) (_hw' : EdgePrimitiveP z w') (_hy : LineEdgeExactP y)
        (_hγ : VertexPrimitiveP (dualityDataP n trivialCharacter) z y γ),
        evalOmega Ω
          ((modelCupP (dualityDataP n trivialCharacter) (a := 1) (b := 1) (m := 3) rfl
              (planeCone z.val.val w'.val) (twistPlane (dualityDataP n trivialCharacter) y.val.val s'.val)).c -
            Ch.map (endRestr .plane) γ) =
        evalOmega Ω
          ((modelCupP (dualityDataP n trivialCharacter) (a := 1) (b := 1) (m := 3) rfl
              (planeCone z.val.val w.val) (twistPlane (dualityDataP n trivialCharacter) y.val.val s.val)).c -
            Ch.map (endRestr .plane) γ) := by
  obtain ⟨Ω, c, hc, H⟩ := traceValueP_eq_evalOmega
  refine ⟨Ω, c, hc, fun {n} z w w' y s s' γ hw hw' hy hγ => ?_⟩
  have h1 := H z w' y s' γ hw' hγ
  have h2 := H z w y s γ hw hγ
  have h3 : traceValueP z w' y = traceValueP z w y :=
    traceValue_eq_of_classesP hw' hw rfl rfl hy
  rw [h1] at h3
  rw [h2] at h3
  exact mul_left_cancel₀ hc h3

/-- The corner cochains `boundaryValue w' y γ` and `boundaryValue w y γ` of two lifts differ by `(w' - w) ⌣ y^φ`, which
evaluates to zero on `Ω`. -/
theorem corner_difference_evalOmega_zero :
    ∃ (Ω : MonoidAlgebra ℚ ((Fin 4 → RationalGL3) × Flag)),
      ∀ {n : ℕ} (z : MaximalCycles n trivialCharacter .line) (w w' : EdgeCochains n trivialCharacter 1)
        (y : MaximalCycles n trivialCharacter .plane) (γ : (Fin 4 → RationalGL3) → Flags .line → ℂ)
        (_hw : EdgePrimitive z w) (_hw' : EdgePrimitive z w') (_hy : PlaneEdgeExact y)
        (_hγ : VertexPrimitive (dualityData n trivialCharacter) z y γ),
        evalOmega Ω (boundaryValue (dualityData n trivialCharacter) w' y γ -
          boundaryValue (dualityData n trivialCharacter) w y γ) = 0 := by
  obtain ⟨Ω, c, hc, H⟩ := cone_pairing_corner_independent
  refine ⟨Ω, fun {n} z w w' y γ hw hw' hy hγ => ?_⟩
  obtain ⟨s, hs⟩ := hy
  have h := H z w w' y s s γ hw hw' ⟨s, hs⟩ hγ
  rw [boundaryValue_eq_cone _ z.val.val w' y s.val γ, boundaryValue_eq_cone _ z.val.val w y s.val γ,
    map_sub]
  exact sub_eq_zero.mpr h

end TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
