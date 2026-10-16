module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Top.BoundaryComparisonGeometry

@[expose] public section


noncomputable section
namespace TernaryPoly.OrdinaryTopBoundaryComparison
open CategoryTheory Limits HomologicalComplex IntegralGL3Congruence
open EquivariantSingularResolution SingularCoverNaturality SingularBoundaryRestriction
open SymmetricSpaceRationalGluing SymmetricSpaceBoundaryIncidenceHomology
open EquivariantMayerVietorisHomology

/-- The actual H0 augmentation of the contractible bordification is an isomorphism. -/
instance upstairsAbsoluteAugmentation_isIso :
    IsIso (homologyAugmentation principalSix (TopCat.of Glued)) := by
  dsimp [homologyAugmentation]
  infer_instance

/-- The whole-boundary inclusion is an H0 isomorphism, with both ends identified by
literal coefficient-sum augmentation. -/
instance upstairsBoundaryH0_isIso : IsIso (homologyMap upstairsBoundaryChainMap 0) := by
  have h : homologyMap upstairsBoundaryChainMap 0 =
      boundaryH0Iso.hom ≫ inv (homologyAugmentation principalSix (TopCat.of Glued)) := by
    apply (cancel_mono (homologyAugmentation principalSix (TopCat.of Glued))).mp
    rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id, boundaryH0Iso_augmentation]
    exact homologyAugmentation_natural boundaryInclusion boundaryInclusion_equivariant
  rw [h]
  infer_instance

/-- The genuine relative pair has zero H0. -/
theorem upstairsRelativeH0_isZero : IsZero (upstairsRelativeChains.homology 0) := by
  let q := homologyMap (cokernel.π upstairsBoundaryChainMap) 0
  have : Epi q := epi_homologyMap_of_epi_of_not_rel _ 0 (by intro j; simp)
  have hq : q = 0 := by
    apply (cancel_epi (homologyMap upstairsBoundaryChainMap 0)).mp
    rw [comp_zero, ← homologyMap_comp, cokernel.condition, homologyMap_zero]
  apply (IsZero.iff_id_eq_zero _).mpr
  apply (cancel_epi q).mp
  rw [Category.comp_id, comp_zero, hq]

/-- The genuine relative pair has zero H1, using the literal connecting map and H0 inclusion. -/
theorem upstairsRelativeH1_isZero : IsZero (upstairsRelativeChains.homology 1) := by
  let δ := upstairsRelativeSequence_shortExact.δ 1 0 rfl
  have : Mono δ := upstairsRelativeSequence_shortExact.mono_δ 1 0 rfl
    (upstairsAbsoluteHomology_isZero 1 (by decide))
  have hδ : δ = 0 := by
    apply (cancel_mono (homologyMap upstairsBoundaryChainMap 0)).mp
    exact (upstairsRelativeSequence_shortExact.δ_comp 1 0 rfl).trans zero_comp.symm
  apply (IsZero.iff_id_eq_zero _).mpr
  apply (cancel_mono δ).mp
  erw [Category.id_comp, zero_comp, hδ]
  rfl

end TernaryPoly.OrdinaryTopBoundaryComparison
