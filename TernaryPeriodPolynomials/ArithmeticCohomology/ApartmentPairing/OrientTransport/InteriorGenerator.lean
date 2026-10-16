module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.OrientTransport.PointTransport
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Locality.SpaceCover
public import TernaryPeriodPolynomials.SymmetricSpace.Relative.FundamentalGeometry

@[expose] public section


/-!
# The interior orientation at a lift

For the interior covering `pS : Space ⟶ (∂)ᶜ` of the arithmetic quotient, the orientation `interiorOrientation` of the interior
at `pS S` is the image of the library local generator of the symmetric space at `S` under the local-homeomorphism map of `pS`.

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory HomologicalComplex TopologicalSpace TernaryPoly TernaryPoly.SymmetricSpaceRelativeFundamental
  TernaryPoly.SymmetricSpaceBordifiedPrincipalSix TernaryPoly.SymmetricSpaceBordifiedQuotient
  TernaryPoly.IntegralGL3Congruence TernaryPoly.SymmetricSpaceQuotientOrientation
  TernaryPoly.SymmetricSpaceCovering TernaryPoly.RationalLocalMap TernaryPoly.RationalLocalOrientation
  TernaryPoly.RationalLocalChartHomology
open TernaryPeriodPolynomials.Argument.Lemma33.Locality

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Lemma33.OrientTransport

theorem interiorHomeomorph_pS (S : TernaryPoly.SymmetricSpacePositive.Space) :
    interiorHomeomorph (pS.hom S) = quotientProjection S := by
  apply arithmeticEmbedding_isOpenEmbedding.injective
  have h1 : arithmeticEmbedding (interiorHomeomorph (pS.hom S)) = ((pS.hom S : ↥(boundary principalSix)ᶜ) : BordifiedOrbit) := by
    have := congrArg Subtype.val (Homeomorph.apply_symm_apply
      arithmeticEmbedding_isOpenEmbedding.isEmbedding.toHomeomorph
      (Homeomorph.setCongr boundary_compl_eq_range (pS.hom S)))
    exact this
  rw [h1, arithmeticEmbedding_projection]
  rfl


theorem quotient_generator_of_eq (f : C(TernaryPoly.SymmetricSpacePositive.Space, OrbitSpace))
    (hf : IsLocalHomeomorph f)
    (h : ∀ z, f z = SymmetricSpaceQuotientOrientation.projection z)
    (S : TernaryPoly.SymmetricSpacePositive.Space) :
    SymmetricSpaceQuotientOrientation.localGenerator (f S) =
      localHomeomorphMap f hf S 5 (SymmetricSpaceLocalOrientation.localGenerator S) := by
  obtain rfl : f = SymmetricSpaceQuotientOrientation.projection := ContinuousMap.ext h
  exact (localGenerator_projection S).symm

/-- **The interior orientation at a lift is the pushforward of the library local orientation of the symmetric space.** -/
theorem interiorOrientation_generator_pS (hpS : IsLocalHomeomorph pS.hom)
    (S : TernaryPoly.SymmetricSpacePositive.Space) :
    interiorOrientation.generator (pS.hom S) =
      localHomeomorphMap pS.hom hpS S 5 (SymmetricSpaceLocalOrientation.localGenerator S) := by
  set b := pS.hom S with hb
  apply (ModuleCat.mono_iff_injective (pointHomologyIso interiorHomeomorph b 5).hom).mp inferInstance
  have hL : (pointHomologyIso interiorHomeomorph b 5).hom (interiorOrientation.generator b) =
      SymmetricSpaceQuotientOrientation.localGenerator (interiorHomeomorph b) := by
    change (pointHomologyIso interiorHomeomorph b 5).hom
      ((pointHomologyIso interiorHomeomorph b 5).inv _) = _
    rw [Iso.inv_hom_id_apply]
    rfl
  rw [hL]
  let e : C(↥(boundary principalSix)ᶜ, OrbitSpace) := ⟨interiorHomeomorph, interiorHomeomorph.continuous⟩
  have hR : (pointHomologyIso interiorHomeomorph b 5).hom
      (localHomeomorphMap pS.hom hpS S 5 (SymmetricSpaceLocalOrientation.localGenerator S)) =
      localHomeomorphMap (e.comp pS.hom) (interiorHomeomorph.isLocalHomeomorph.comp hpS) S 5
        (SymmetricSpaceLocalOrientation.localGenerator S) := by
    rw [← localHomeomorphMap_comp pS.hom e hpS interiorHomeomorph.isLocalHomeomorph S 5]
    change (homologyMap (homeomorphLocalIso interiorHomeomorph b).hom 5)
      (localHomeomorphMap pS.hom hpS S 5 (SymmetricSpaceLocalOrientation.localGenerator S)) = _
    rw [← localHomeomorphMap_homeomorph interiorHomeomorph b 5]
    rfl
  rw [hR]
  exact quotient_generator_of_eq (e.comp pS.hom) (interiorHomeomorph.isLocalHomeomorph.comp hpS)
    (fun z => interiorHomeomorph_pS z) S


/-- **The interior covering `pS` is a local homeomorphism.** -/
theorem pS_isLocalHomeomorph : IsLocalHomeomorph pS.hom := by
  have h : (pS.hom : TernaryPoly.SymmetricSpacePositive.Space → ↥(boundary principalSix)ᶜ) =
      interiorHomeomorph.symm ∘ SymmetricSpaceQuotientOrientation.projection :=
    funext fun S => by
      rw [Function.comp_apply]
      exact (interiorHomeomorph.eq_symm_apply.mpr (interiorHomeomorph_pS S)).symm
  rw [h]
  exact interiorHomeomorph.symm.isLocalHomeomorph.comp projection_localHomeomorph

end TernaryPeriodPolynomials.Argument.Lemma33.OrientTransport
