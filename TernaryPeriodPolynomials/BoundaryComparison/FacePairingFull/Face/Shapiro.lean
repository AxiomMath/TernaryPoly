module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Face.Cusps
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.FacePairingForm
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairing.CuspFlagDisjoint
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairing.ShapiroRealization

@[expose] public section


/-!
# Inner classes of a side are the direct sum of the locally inner classes at its two reference flags

For a good flag `Fgood` and a bad flag `Fbad` of one side, the map
`b ↦ (fixedPointH2 Fgood b, fixedPointH2 Fbad b)` is a linear isomorphism
`innerClasses n side ≃ locallyInnerClasses Fgood × locallyInnerClasses Fbad`
(`innerClassesEquivLocal`). Injectivity is the joint detection of zero at the two cusps; surjectivity
is Shapiro realization of each local class by a global class vanishing at the other orbit. Combined
with `Face/CuspIso` this expresses `innerClasses n side` as the direct sum of the two mixed
cuspidal groups of the side.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

open GeneralEisenstein Homogeneous
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.Spectral.CuspOrbits
open TernaryPeriodPolynomials.Argument.FacePairing

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Face

/-- Two flags of the same goodness are translates under the level group. -/
theorem exists_level_smul_of_good_iff {side : Side} (F₁ F₂ : Flags side)
    (h : GoodFlag side F₁ ↔ GoodFlag side F₂) :
    ∃ γ : rationalLevel, γ.val • F₁ = F₂ := by
  classical
  have hobtain1 := cuspFlag_transporter side (decide (GoodFlag side F₁)) F₁ (by simp)
  obtain ⟨γ₁, h₁⟩ := hobtain1
  have hobtain2 := cuspFlag_transporter side (decide (GoodFlag side F₁)) F₂ (by simp [← h])
  obtain ⟨γ₂, h₂⟩ := hobtain2
  generalize cuspFlag side (decide (GoodFlag side F₁)) = c at h₁ h₂
  refine ⟨γ₂ * γ₁⁻¹, ?_⟩
  rw [← h₂, ← h₁]
  change (γ₂.val * γ₁.val⁻¹) • (γ₁.val • c) = _
  rw [smul_smul, mul_assoc, inv_mul_cancel, mul_one]

/-- Flags of different goodness are never translates. -/
theorem not_level_smul_of_good_ne {side : Side} (F₁ F₂ : Flags side)
    (h : GoodFlag side F₁) (h' : ¬ GoodFlag side F₂) :
    ¬ ∃ γ : rationalLevel, γ.val • F₂ = F₁ := by
  rintro ⟨γ, hγ⟩
  exact h' ((goodFlag_smul_rationalLevel γ F₂).mp (hγ ▸ h))

variable (n : ℕ) {side : Side} (Fgood Fbad : Flags side)

/-- Shapiro coordinates of an inner class at the two reference flags. -/
def innerToLocal (hgood : GoodFlag side Fgood) (hbad : ¬ GoodFlag side Fbad) :
    innerClasses n side →ₗ[ℂ]
      locallyInnerClasses n trivialCharacter side Fgood ×
        locallyInnerClasses n trivialCharacter side Fbad :=
  LinearMap.prod
    (((fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter) Fgood).comp
      (innerClasses n side).subtype).codRestrict _ fun b =>
        ((innerBoundary_iff_locallyInner_reps Fgood Fbad hgood hbad b.val).mp b.property).1)
    (((fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter) Fbad).comp
      (innerClasses n side).subtype).codRestrict _ fun b =>
        ((innerBoundary_iff_locallyInner_reps Fgood Fbad hgood hbad b.val).mp b.property).2)

theorem innerToLocal_injective (hgood : GoodFlag side Fgood) (hbad : ¬ GoodFlag side Fbad) :
    Function.Injective (innerToLocal n Fgood Fbad hgood hbad) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro b hb
  have h1 : fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter) Fgood
      b.val = 0 := congrArg Subtype.val (congrArg Prod.fst hb)
  have h0 : fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter) Fbad
      b.val = 0 := congrArg Subtype.val (congrArg Prod.snd hb)
  apply Subtype.ext
  refine (eq_zero_iff_fixedPointH2 rationalLevel _ b.val).mpr fun flag => ?_
  by_cases hg : GoodFlag side flag
  · obtain ⟨γ, hγ⟩ := exists_level_smul_of_good_iff Fgood flag ⟨fun _ => hg, fun _ => hgood⟩
    rw [← stabilizerTransportH2_fixedPointH2 rationalLevel
      (rationalCoefficientComponent n trivialCharacter) γ Fgood flag hγ b.val, h1, map_zero]
  · obtain ⟨γ, hγ⟩ := exists_level_smul_of_good_iff Fbad flag
      ⟨fun h => absurd h hbad, fun h => absurd h hg⟩
    rw [← stabilizerTransportH2_fixedPointH2 rationalLevel
      (rationalCoefficientComponent n trivialCharacter) γ Fbad flag hγ b.val, h0, map_zero]

theorem innerToLocal_surjective (hgood : GoodFlag side Fgood) (hbad : ¬ GoodFlag side Fbad) :
    Function.Surjective (innerToLocal n Fgood Fbad hgood hbad) := by
  intro target
  obtain ⟨⟨u, hu⟩, ⟨v, hv⟩⟩ := target
  have hobtain3 := Submodule.mkQ_surjective (LinearMap.range
    (boundaryMap (fixedPointLevel rationalLevel Fgood)
      (rationalCoefficientComponent n trivialCharacter))) u
  obtain ⟨cu, hcu⟩ := hobtain3
  have hobtain4 := Submodule.mkQ_surjective (LinearMap.range
    (boundaryMap (fixedPointLevel rationalLevel Fbad)
      (rationalCoefficientComponent n trivialCharacter))) v
  obtain ⟨cv, hcv⟩ := hobtain4
  have hobtain5 := shapiro_realization rationalLevel
    (rationalCoefficientComponent n trivialCharacter) Fgood cu
  obtain ⟨ξu, hξu, hξu0⟩ := hobtain5
  have hobtain6 := shapiro_realization rationalLevel
    (rationalCoefficientComponent n trivialCharacter) Fbad cv
  obtain ⟨ξv, hξv, hξv0⟩ := hobtain6
  have hu0 : fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter) Fbad ξu
      = 0 := hξu0 Fbad fun ⟨γ, hγ⟩ =>
    not_level_smul_of_good_ne Fgood Fbad hgood hbad ⟨γ⁻¹, by
      rw [Subgroup.coe_inv, ← hγ]
      exact inv_smul_smul _ _⟩
  have hv0 : fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter) Fgood ξv
      = 0 := hξv0 Fgood (not_level_smul_of_good_ne Fgood Fbad hgood hbad)
  have hsum1 : fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter) Fgood
      (ξu + ξv) = u := by
    rw [map_add, hξu, hv0, add_zero]; exact hcu
  have hsum0 : fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter) Fbad
      (ξu + ξv) = v := by
    rw [map_add, hu0, hξv, zero_add]; exact hcv
  have inner : InnerBoundary n trivialCharacter side (ξu + ξv) :=
    (innerBoundary_iff_locallyInner_reps Fgood Fbad hgood hbad _).mpr
      ⟨hsum1 ▸ hu, hsum0 ▸ hv⟩
  refine ⟨⟨ξu + ξv, inner⟩, ?_⟩
  apply Prod.ext
  · exact Subtype.ext hsum1
  · exact Subtype.ext hsum0

/-- **`innerClasses n side ≃ locallyInner(Fgood) × locallyInner(Fbad)`.** -/
def innerClassesEquivLocal (hgood : GoodFlag side Fgood) (hbad : ¬ GoodFlag side Fbad) :
    innerClasses n side ≃ₗ[ℂ]
      locallyInnerClasses n trivialCharacter side Fgood ×
        locallyInnerClasses n trivialCharacter side Fbad :=
  LinearEquiv.ofBijective (innerToLocal n Fgood Fbad hgood hbad)
    ⟨innerToLocal_injective n Fgood Fbad hgood hbad,
      innerToLocal_surjective n Fgood Fbad hgood hbad⟩

end TernaryPeriodPolynomials.Argument.FacePairingFull.Face
