module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.DualJ.DualSeries
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.StokesPairing

@[expose] public section


/-!
# The Stokes lemma `ar:lem:stokes` in the paper's form, with the ȷ-dual class

For `a ∈ H²(X_Γ, E)` and `b ∈ H²(X_Γ, E*)` with mixed cuspidal maximal-face restrictions and zero
restrictions on all flag strata, `⟨r_P a, r_P b⟩_P + ⟨r_Q a, r_Q b⟩_Q = 0`, "the orientations are included in the two pairings".

In the model the dual coefficient system is `E* = E ∘ φ`, the dual class attached to an `E`-class `c'` is its `ȷ`-pullback
`jDualCocycle c'` (`DualJ.DualSeries`), and the pairing of `C_R(E)` with `C_R(E*)` is the cochain face pairing against the
inner `E`-class obtained by the transport `fromPlaneStar` / `fromLineStar` of the face component of `b`. `paper_stokes` states the paper's relation with these pairings.

**Orientation signs.** The model pairings are `⟨ξ, ζ⟩_P := facePairingP ξ ζ` and `⟨ξ, ζ⟩_Q := facePairing ξ ζ`, both defined from
one boundary trace of the mapping-cone cocycle `(α, β, u)` with the cone sign `d(α, β, u) = (dα, dβ, α|_{F_B} - β|_{F_B} - du)`
of the paper: the plane face enters the boundary cycle with `+`, the line face with `-`. Hence the model identity of
`StokesPairing` reads `⟨ , ⟩_P = ⟨ , ⟩_Q`, and the paper's relation, in which each pairing carries the orientation of its
face, holds for `⟨ , ⟩_P` and the negated `⟨ , ⟩_Q`: the face orientation character that the paper includes in `⟨ , ⟩_Q`
relative to the model is the sign `-1` forced by the cone convention. This is the only orientation information in the model;
a comparison with the orientation of the oriented faces of the Borel-Serre boundary requires face fundamental classes and de Rham
integration over faces, which are not in the library (the whole-boundary evaluation is `Statements.TraceComparison`).

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.Argument.FacePairingFull
open TernaryPeriodPolynomials.Argument.FacePairingFull.Dual
open TernaryPeriodPolynomials.Argument.FacePairingFull.DualJ

namespace TernaryPeriodPolynomials.Argument.FacePairingFull

variable {n : ℕ}

theorem fromPlaneStar_restriction_phi
    (c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter)) :
    fromPlaneStar (rationalCoefficientComponent n trivialCharacter)
        (restrictionCocycleRep (dualRep (rationalCoefficientComponent n trivialCharacter)) .plane
          (jDualCocycle (rationalCoefficientComponent n trivialCharacter) c)) =
      restrictionCocycle n trivialCharacter .line c := by
  rw [jDualCocycle_eq_phi, ← toPlaneStar_restriction, fromPlaneStar_toPlaneStar]
  rfl

theorem fromLineStar_restriction_phi
    (c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter)) :
    fromLineStar (rationalCoefficientComponent n trivialCharacter)
        (restrictionCocycleRep (dualRep (rationalCoefficientComponent n trivialCharacter)) .line
          (jDualCocycle (rationalCoefficientComponent n trivialCharacter) c)) =
      restrictionCocycle n trivialCharacter .plane c := by
  rw [jDualCocycle_eq_phi, ← toLineStar_restriction, fromLineStar_toLineStar]
  rfl

theorem paper_stokes_aux {P Q P' Q' : ℂ} (hP : P = P') (hQ : Q = Q') (h : P' = Q') : P + -Q = 0 := by
  rw [hP, hQ, h]
  exact add_neg_cancel _

/-- **The Stokes lemma `ar:lem:stokes` (paper form).** For global classes `a = c` of `E` and `b = jDualCocycle c'` of `E*` with
zero flag restrictions, `⟨r_P a, r_P b⟩_P + ⟨r_Q a, r_Q b⟩_Q = 0`, where `⟨ , ⟩_P` is `facePairingP`, `⟨ , ⟩_Q` is
minus `facePairing` (orientation sign of the cone convention. -/
theorem paper_stokes
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
          (fromPlaneStar (rationalCoefficientComponent n trivialCharacter)
            (restrictionCocycleRep (dualRep (rationalCoefficientComponent n trivialCharacter)) .plane
              (jDualCocycle (rationalCoefficientComponent n trivialCharacter) c'))),
          by
            rw [fromPlaneStar_restriction_phi]
            exact innerBoundary_restriction_of_exact c' w' hw' .line⟩ +
      -facePairing n
        ⟨classOf rationalLevel
          (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line)
          (restrictionCocycle n trivialCharacter .line c),
          innerBoundary_restriction_of_exact c w hw .line⟩
        ⟨classOf rationalLevel
          (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane)
          (fromLineStar (rationalCoefficientComponent n trivialCharacter)
            (restrictionCocycleRep (dualRep (rationalCoefficientComponent n trivialCharacter)) .line
              (jDualCocycle (rationalCoefficientComponent n trivialCharacter) c'))),
          by
            rw [fromLineStar_restriction_phi]
            exact innerBoundary_restriction_of_exact c' w' hw' .plane⟩ = 0 := by
  have h := facePairingP_global_eq_facePairing_global c c' w w' hw hw'
  have e1 : (⟨classOf rationalLevel
          (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line)
          (fromPlaneStar (rationalCoefficientComponent n trivialCharacter)
            (restrictionCocycleRep (dualRep (rationalCoefficientComponent n trivialCharacter)) .plane
              (jDualCocycle (rationalCoefficientComponent n trivialCharacter) c'))),
          by
            rw [fromPlaneStar_restriction_phi]
            exact innerBoundary_restriction_of_exact c' w' hw' .line⟩ : innerClasses n .line) =
      ⟨classOf rationalLevel
          (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line)
          (restrictionCocycle n trivialCharacter .line c'),
          innerBoundary_restriction_of_exact c' w' hw' .line⟩ :=
    by
      apply Subtype.ext
      exact congrArg (classOf rationalLevel (flagRepresentation
        (rationalCoefficientComponent n trivialCharacter) .line)) (fromPlaneStar_restriction_phi c')
  have e2 : (⟨classOf rationalLevel
          (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane)
          (fromLineStar (rationalCoefficientComponent n trivialCharacter)
            (restrictionCocycleRep (dualRep (rationalCoefficientComponent n trivialCharacter)) .line
              (jDualCocycle (rationalCoefficientComponent n trivialCharacter) c'))),
          by
            rw [fromLineStar_restriction_phi]
            exact innerBoundary_restriction_of_exact c' w' hw' .plane⟩ : innerClasses n .plane) =
      ⟨classOf rationalLevel
          (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane)
          (restrictionCocycle n trivialCharacter .plane c'),
          innerBoundary_restriction_of_exact c' w' hw' .plane⟩ :=
    by
      apply Subtype.ext
      exact congrArg (classOf rationalLevel (flagRepresentation
        (rationalCoefficientComponent n trivialCharacter) .plane)) (fromLineStar_restriction_phi c')
  exact paper_stokes_aux (congrArg (Plane.facePairingP n _) e1) (congrArg (facePairing n _) e2) h

end TernaryPeriodPolynomials.Argument.FacePairingFull
