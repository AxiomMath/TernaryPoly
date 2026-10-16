module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Plane.Pairing
public import TernaryPeriodPolynomials.BoundaryComparison.FaceRestriction.Cocycles

@[expose] public section


/-!
# Stokes (Lemma C.2) as an identity between the two face pairings

For global cocycles `c, c'` of `E` that vanish on the complete flags (edge primitives `w, w'`) the
restrictions `r_P c, r_Q c, r_P c', r_Q c'` are inner classes, and the exactness of `face_pairing_stokes`
becomes the identity of bilinear forms

`⟨ r_P c , r_Q c' ⟩_P = ⟨ r_Q c , r_P c' ⟩_Q`

(`facePairingP_global_eq_facePairing_global`). In the model the second constant-term map of the dual
coefficient system `E*` is the transport of the first, so this is the model form of the paper's
`⟨ ξ , T^∨ η ⟩_P = - ⟨ T ξ , η ⟩_Q`.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.BoundaryDuality.TraceRepresentatives
open TernaryPeriodPolynomials.BoundaryDuality.TraceReduction
open TernaryPeriodPolynomials.BoundaryDuality.L2Trace
  (traceDataL2 isBoundaryTrace_traceDataL2)
open TernaryPeriodPolynomials.BoundaryDuality.StabilizerVanishing
  (lineCupExact)

namespace TernaryPeriodPolynomials.Argument.FacePairingFull

variable {n : ℕ}

/-- The restriction of an edge-exact global cocycle to a maximal stratum is an inner class. -/
theorem innerBoundary_restriction_of_exact
    (c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter))
    (w : EdgeCochains n trivialCharacter 1)
    (hw : ∀ x e, c.val.val x = differentialOneRaw w.val x e) (side : Side) :
    InnerBoundary n trivialCharacter side
      (classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent n trivialCharacter) side)
        (restrictionCocycle n trivialCharacter side c)) :=
  ⟨restrictionCocycle n trivialCharacter side c, rfl, w, fun x e => hw x e⟩

/-- **Stokes in the model.** For edge-exact global cocycles `c, c'` of `E`,
`⟨ r_P c , r_Q c' ⟩_P = ⟨ r_Q c , r_P c' ⟩_Q`. -/
theorem facePairingP_global_eq_facePairing_global
    (c c' : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter))
    (w w' : EdgeCochains n trivialCharacter 1)
    (hw : ∀ x e, c.val.val x = differentialOneRaw w.val x e)
    (hw' : ∀ x e, c'.val.val x = differentialOneRaw w'.val x e) :
    Plane.facePairingP n
        ⟨classOf rationalLevel
          (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane)
          (restrictionCocycle n trivialCharacter .plane c),
          innerBoundary_restriction_of_exact c w hw .plane⟩
        ⟨classOf rationalLevel
          (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line)
          (restrictionCocycle n trivialCharacter .line c'),
          innerBoundary_restriction_of_exact c' w' hw' .line⟩ =
      facePairing n
        ⟨classOf rationalLevel
          (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line)
          (restrictionCocycle n trivialCharacter .line c),
          innerBoundary_restriction_of_exact c w hw .line⟩
        ⟨classOf rationalLevel
          (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane)
          (restrictionCocycle n trivialCharacter .plane c'),
          innerBoundary_restriction_of_exact c' w' hw' .plane⟩ := by
  refine (Plane.facePairing_apply_eqP (z := restrictionCocycle n trivialCharacter .plane c)
    (w := w) (y := restrictionCocycle n trivialCharacter .line c') rfl (fun x e => hw x e)
    rfl).trans (Eq.trans ?_ (facePairing_apply_eq (z := restrictionCocycle n trivialCharacter .line c)
    (w := w) (y := restrictionCocycle n trivialCharacter .plane c') rfl (fun x e => hw x e)
    rfl).symm)
  obtain ⟨γP, hγP⟩ := Plane.planeCupExact_unconditionalP (Plane.dualityDataP n trivialCharacter)
    (restrictionCocycle n trivialCharacter .plane c) (restrictionCocycle n trivialCharacter .line c')
  obtain ⟨γQ, hγQ⟩ := lineCupExact (dualityData n trivialCharacter)
    (restrictionCocycle n trivialCharacter .line c) (restrictionCocycle n trivialCharacter .plane c')
  rw [← Plane.trace_boundaryValue_eq_traceValueP hγP, ← trace_boundaryValue_eq_traceValue hγQ]
  have hexact := TernaryPeriodPolynomials.Argument.Classification.face_pairing_stokes n c c' w
    (fun x e => hw x e) γP hγP.1 (fun x F => hγP.2 x F) γQ hγQ.1 (fun x F => hγQ.2 x F)
  have hzero : traceDataL2.trace.toAddMonoidHom
      (fun x e => (dualPairing n (w.val ![x 0, x 1] e)
          (c'.val.val ![dualInvolution (x 1), dualInvolution (x 2), dualInvolution (x 3)]) -
        γP x (endpoint .plane e)) -
      (dualPairing n (w.val ![x 0, x 1] e)
          (c'.val.val ![dualInvolution (x 1), dualInvolution (x 2), dualInvolution (x 3)]) -
        γQ x (endpoint .line e))) = 0 := by
    by_contra hne
    exact not_boundaryExact_of_trace isBoundaryTrace_traceDataL2 hne hexact
  change traceDataL2.trace.toAddMonoidHom
    (Plane.boundaryValueP (Plane.dualityDataP n trivialCharacter) w
        (restrictionCocycle n trivialCharacter .line c') γP -
      boundaryValue (dualityData n trivialCharacter) w
        (restrictionCocycle n trivialCharacter .plane c') γQ) = 0 at hzero
  rw [map_sub] at hzero
  exact sub_eq_zero.mp hzero

end TernaryPeriodPolynomials.Argument.FacePairingFull
