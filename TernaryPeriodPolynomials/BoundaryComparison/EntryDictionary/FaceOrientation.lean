module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Glue.Main
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.StokesPairing

@[expose] public section


/-!
# The orientation dictionary of the oriented boundary faces

Formalized by Claude Sonnet 5.5.

Facts used (proved elsewhere, cited by name).

* `Glue.facePairing_glue`: there are a quasi-isomorphism `Ψ : coneR ⟶ boundaryChains` over the augmentation and one
  nonzero constant `c` such that the model line pairing `⟨ , ⟩_Q = facePairing n` equals `c` times the geometric pairing of the
  `Ψ`-pullbacks (`LineGlue Ψ c`) and the model plane pairing `⟨ , ⟩_P = facePairingP n` equals `-c` times it (`PlaneGlue Ψ (-c)`).
* `facePairingP_global_eq_facePairing_global` (model Stokes, Lemma C.2 for the cone): `⟨r_P c, r_Q c'⟩_P = ⟨r_Q c, r_P c'⟩_Q`.

**Orientation dictionary** (this file).  The face orientation character that the paper includes in `⟨ , ⟩_R` is the sign relating
the model pairing of the face to the geometric pairing of the oriented boundary: `+c⁻¹` for the line face `Q` and `(-c)⁻¹` for the plane
face `P`, with the SAME `c`.  In this normalization the model Stokes identity is exactly the paper's relation
`⟨r_P a, r_P b⟩_P + ⟨r_Q a, r_Q b⟩_Q = 0` (`oriented_stokes`); the relative sign of the two faces is thus determined (it is the sign
of the cone differential `d(α, β, u) = (dα, dβ, α|_{F_B} - β|_{F_B} - du)`: plane `+`, line `-`), while the absolute sign of `c` is the
orientation of the comparison `Ψ` with the boundary fundamental class (a normalization: a different orientation of the boundary or of the
cellular/Gram fundamental cycle multiplies `c` by `-1` and leaves every statement above, being homogeneous in `c`, unchanged;
`oriented_stokes_scale`).
-/

noncomputable section

open CategoryTheory Limits
open TernaryPoly.SymmetricSpaceBoundaryIncidenceHomology (boundaryChains ambient)
open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
open GeneralEisenstein GeneralEisenstein.Homogeneous TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.Argument.FacePairingFull
open TernaryPeriodPolynomials.Argument.FacePairingFull.Glue

namespace TernaryPeriodPolynomials.Argument.EntryDictionary

/-- The model plane pairing `⟨ r_P c , r_Q c' ⟩_P` of edge-exact global cocycles. -/
def modelPlanePairing {n : ℕ}
    (c c' : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter))
    (w w' : EdgeCochains n trivialCharacter 1)
    (hw : ∀ x e, c.val.val x = differentialOneRaw w.val x e)
    (hw' : ∀ x e, c'.val.val x = differentialOneRaw w'.val x e) : ℂ :=
  Plane.facePairingP n
    ⟨classOf rationalLevel
      (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane)
      (restrictionCocycle n trivialCharacter .plane c),
      innerBoundary_restriction_of_exact c w hw .plane⟩
    ⟨classOf rationalLevel
      (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line)
      (restrictionCocycle n trivialCharacter .line c'),
      innerBoundary_restriction_of_exact c' w' hw' .line⟩

/-- The model line pairing `⟨ r_Q c , r_P c' ⟩_Q` of edge-exact global cocycles. -/
def modelLinePairing {n : ℕ}
    (c c' : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter))
    (w w' : EdgeCochains n trivialCharacter 1)
    (hw : ∀ x e, c.val.val x = differentialOneRaw w.val x e)
    (hw' : ∀ x e, c'.val.val x = differentialOneRaw w'.val x e) : ℂ :=
  facePairing n
    ⟨classOf rationalLevel
      (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line)
      (restrictionCocycle n trivialCharacter .line c),
      innerBoundary_restriction_of_exact c w hw .line⟩
    ⟨classOf rationalLevel
      (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane)
      (restrictionCocycle n trivialCharacter .plane c'),
      innerBoundary_restriction_of_exact c' w' hw' .plane⟩

/-- **Model Stokes** (`ar:lem:stokes` for the cone): the two model face pairings of edge-exact global cocycles agree. -/
theorem model_stokes {n : ℕ}
    (c c' : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter))
    (w w' : EdgeCochains n trivialCharacter 1)
    (hw : ∀ x e, c.val.val x = differentialOneRaw w.val x e)
    (hw' : ∀ x e, c'.val.val x = differentialOneRaw w'.val x e) :
    modelPlanePairing c c' w w' hw hw' = modelLinePairing c c' w w' hw hw' :=
  facePairingP_global_eq_facePairing_global c c' w w' hw hw'

/-- **The oriented Stokes relation** `⟨r_P a, r_P b⟩_P + ⟨r_Q a, r_Q b⟩_Q = 0`: with the face orientations `(-c)⁻¹` (plane) and `c⁻¹`
(line) of the glue constants, the model Stokes identity is the paper's. -/
theorem oriented_stokes {n : ℕ} (κ : ℂ)
    (c c' : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter))
    (w w' : EdgeCochains n trivialCharacter 1)
    (hw : ∀ x e, c.val.val x = differentialOneRaw w.val x e)
    (hw' : ∀ x e, c'.val.val x = differentialOneRaw w'.val x e) :
    (-κ)⁻¹ * modelPlanePairing c c' w w' hw hw' + κ⁻¹ * modelLinePairing c c' w w' hw hw' = 0 := by
  rw [model_stokes c c' w w' hw hw', inv_neg]
  ring

/-- The oriented relation is homogeneous in the glue constant: replacing `κ` by `μ κ` (a different orientation or normalization of
the fundamental cycle) multiplies both oriented pairings by `μ⁻¹` and preserves the relation. -/
theorem oriented_stokes_scale {n : ℕ} (κ μ : ℂ)
    (c c' : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter))
    (w w' : EdgeCochains n trivialCharacter 1)
    (hw : ∀ x e, c.val.val x = differentialOneRaw w.val x e)
    (hw' : ∀ x e, c'.val.val x = differentialOneRaw w'.val x e) :
    (-(μ * κ))⁻¹ * modelPlanePairing c c' w w' hw hw' + (μ * κ)⁻¹ * modelLinePairing c c' w w' hw hw' =
      μ⁻¹ * ((-κ)⁻¹ * modelPlanePairing c c' w w' hw hw' + κ⁻¹ * modelLinePairing c c' w w' hw hw') := by
  rw [inv_neg, inv_neg, mul_inv]
  ring

/-- **The face orientation dictionary.**  There are a comparison `Ψ` of the cone with the boundary chains and one constant `c ≠ 0` such
that the model line pairing is `c` times the geometric pairing, the model plane pairing is `-c` times it (`facePairing_glue`), and in this
normalization the Stokes relation holds (`oriented_stokes`). -/
theorem face_orientation_dictionary :
    ∃ (Ψ : coneR ⟶ boundaryChains) (c : ℂ), QuasiIso Ψ ∧ Ψ ≫ augB = augR ∧ c ≠ 0 ∧
      LineGlue Ψ c ∧ PlaneGlue Ψ (-c) ∧
      ∀ {n : ℕ} (c₁ c₁' : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter))
        (w w' : EdgeCochains n trivialCharacter 1)
        (hw : ∀ x e, c₁.val.val x = differentialOneRaw w.val x e)
        (hw' : ∀ x e, c₁'.val.val x = differentialOneRaw w'.val x e),
        (-c)⁻¹ * modelPlanePairing c₁ c₁' w w' hw hw' + c⁻¹ * modelLinePairing c₁ c₁' w w' hw hw' = 0 := by
  obtain ⟨Ψ, c, hq, haug, hc, hL, hP⟩ := facePairing_glue
  exact ⟨Ψ, c, hq, haug, hc, hL, hP, fun {n} c₁ c₁' w w' hw hw' => oriented_stokes c c₁ c₁' w w' hw hw'⟩

end TernaryPeriodPolynomials.Argument.EntryDictionary
