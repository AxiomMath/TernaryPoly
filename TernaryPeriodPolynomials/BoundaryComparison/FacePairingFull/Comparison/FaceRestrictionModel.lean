module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Dual.Model
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelTransfer.Bridge
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.CuspReduction

@[expose] public section


/-!
# The model coordinates of a global class are the restrictions to the stabilizers of the flags

The boundary coordinates `(r_P, r_Q)` of the cochain model pull a global cocycle back to the strata
`Fun(Flags s, E)` as a function that is literally constant on flags (`restrictionCocycleRep`), and the
Shapiro coordinate at a flag `F` (`fixedPointH2`, `cuspRes` for the reference cusps) evaluates a stratum
cocycle at `F` on the stabilizer `Γ_F = Γ ⊓ Stab F`.  This file shows that the composite is the
*plain restriction of group cohomology* to the stabilizer of the flag, `faceRestriction`
(`resH2` along `Γ_F ≤ Γ`): for every flag, every global class `a` and every coefficient system `ρ`
`fixedPointH2 F (r_s a) = faceRestriction F a`.  With Mathlib's group cohomology this is the restriction
`groupCohomology.map` along `Γ_F ↪ Γ` (`bridge_faceRestriction`).

Formalized by Claude Sonnet 5.5.
-/

open GeneralEisenstein GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.Argument.LevelTransfer
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.Argument.FacePairingFull.Dual

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison

variable {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ RationalGL3 V)

theorem fixedPointLevel_le {X : Type} [MulAction RationalGL3 X] (x : X) :
    fixedPointLevel rationalLevel x ≤ rationalLevel := inf_le_left

/-- **The restriction of a global class to the stabilizer of a flag** (or of any point of a
`GL₃(ℚ)`-set): ordinary restriction of group cohomology `H²(Γ, ρ) → H²(Γ_F, ρ)`. -/
def faceRestriction {X : Type} [MulAction RationalGL3 X] (x : X) :
    H2 rationalLevel ρ →ₗ[ℂ] H2 (fixedPointLevel rationalLevel x) ρ :=
  resH2 ρ (fixedPointLevel_le x)

/-- The Shapiro coordinate of the constant-on-flags restriction of a global cocycle is the restriction
of the global class to the stabilizer. -/
theorem fixedPointH2_restrictionCocycleRep (s : Side) (F : Flags s) (c : cocycles rationalLevel ρ) :
    fixedPointH2 rationalLevel ρ F
        (classOf rationalLevel (flagRepresentation ρ s) (restrictionCocycleRep ρ s c)) =
      faceRestriction ρ F (classOf rationalLevel ρ c) := rfl

/-- On classes: `fixedPointH2 F ∘ r_s = faceRestriction F`, where `r_s` is the class-level restriction
to the stratum of any linear map realizing the constant-on-flags restriction. -/
theorem fixedPointH2_stratum_eq (s : Side) (F : Flags s)
    (r : H2 rationalLevel ρ →ₗ[ℂ] H2 rationalLevel (flagRepresentation ρ s))
    (hr : ∀ c, r (classOf rationalLevel ρ c) =
      classOf rationalLevel (flagRepresentation ρ s) (restrictionCocycleRep ρ s c))
    (a : H2 rationalLevel ρ) :
    fixedPointH2 rationalLevel ρ F (r a) = faceRestriction ρ F a := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  have e : (Submodule.Quotient.mk c : H2 rationalLevel ρ) = classOf rationalLevel ρ c := rfl
  rw [e, hr c]
  rfl

/-- The reference-cusp Shapiro coordinate (`cuspRes`) of a boundary coordinate of a global class is the
restriction of the class to the cusp stabilizer. -/
theorem cuspRes_restrictionCocycle (n : ℕ) (χ : RankOneCharacter) (s : Side) (good : Bool)
    (c : cocycles rationalLevel (rationalCoefficientComponent n χ)) :
    TernaryPeriodPolynomials.Spectral.CuspReduction.cuspRes n χ s good
        (classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) s)
          (restrictionCocycle n χ s c)) =
      faceRestriction (rationalCoefficientComponent n χ)
        (TernaryPeriodPolynomials.Spectral.CuspOrbits.cuspFlag s good)
        (classOf rationalLevel (rationalCoefficientComponent n χ) c) := rfl

/-- **Naturality of the bridge**: under the identification of the homogeneous-cochain model with
Mathlib's group cohomology, `faceRestriction` is `groupCohomology.map` along the inclusion
`Γ_F ↪ Γ`. -/
theorem bridge_faceRestriction {X : Type} [MulAction RationalGL3 X] (x : X)
    (a : H2 rationalLevel ρ) :
    (groupCohomology.map (Subgroup.inclusion (fixedPointLevel_le x))
        (resRep ρ (fixedPointLevel_le x)) 2).hom (bridge ρ rationalLevel a) =
      bridge ρ (fixedPointLevel rationalLevel x) (faceRestriction ρ x a) :=
  bridge_res ρ (fixedPointLevel_le x) a

end TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
