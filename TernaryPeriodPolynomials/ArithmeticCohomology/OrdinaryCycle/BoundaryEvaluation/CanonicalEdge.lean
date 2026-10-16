module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.BoundaryEvaluation.GeometricRestriction

@[expose] public section

noncomputable section
namespace TernaryPoly.OrdinaryBoundaryActualEvaluation
open CategoryTheory Limits HomologicalComplex BoundaryFaceResolutionComparison Preadditive
open IntegralGL3Congruence SymmetricSpaceBoundaryFullTransfer SymmetricSpaceBoundaryFull
open SymmetricSpaceBoundaryFaceAugmentation SymmetricSpaceBoundaryIncidenceHomology

/-- The complete forward full-face/canonical comparison preserves the literal augmented corner cochain. -/
theorem fullFaceCanonical_cornerCochain :
    (fullFaceConeParabolicEquiv.hom ≫ parabolicCanonicalEquiv.hom).f 1 ≫
      coneCornerCochain canonicalFaceArrow fullFlagLabels (flagParabolicResolution.π.f 0) =
    coneCornerCochain fullFaceArrow fullFlagLabels (fullFlagResolution.π.f 0) := by
  have hp := coneComparison_corner parabolicFaceArrow fullFlagLabels (flagParabolicResolution.π.f 0)
    canonicalFaceArrow (𝟙 _) (𝟙 _) canonicalFaceSquare (flagParabolicResolution.π.f 0)
    (Category.id_comp _)
  have hf := coneComparison_corner fullFaceArrow fullFlagLabels (fullFlagResolution.π.f 0)
    parabolicFaceArrow flagParabolicComparison.hom parabolicMiddleComparison parabolicFaceSquare
    (flagParabolicResolution.π.f 0) fullFlagParabolic_augmentation
  rw [fullFaceConeParabolicEquiv_hom, parabolicCanonicalEquiv_hom]
  change (fullFaceConeToParabolic.f 1 ≫ parabolicToCanonical.f 1) ≫ _ = _
  erw [Category.assoc, hp, hf]

/-- The complete canonical corner evaluator on the actual principal-six restriction. -/
def restrictedCanonicalCorner : (restrictedComplex principalSix canonicalFaceCone).homology 1 ⟶ flagLabels :=
  restrictedEvaluation principalSix canonicalFaceCone fullFlagLabels 1
    (coneCornerCochain canonicalFaceArrow fullFlagLabels (flagParabolicResolution.π.f 0))
    (coneCornerCochain_boundary canonicalFaceArrow fullFlagLabels (flagParabolicResolution.π.f 0)
      flagParabolicResolution.complex_d_comp_π_f_zero)

/-- The full face/canonical comparison retains the actual evaluator after restriction. -/
theorem restrictedFullFaceCanonical_corner :
    homologyMap (coverRestrictionFunctor.map
      (fullFaceConeParabolicEquiv.hom ≫ parabolicCanonicalEquiv.hom)) 1 ≫
      restrictedCanonicalCorner = restrictedFullCorner := by
  apply restrictedEvaluation_natural
  exact fullFaceCanonical_cornerCochain

/-- The actual restricted boundary/canonical equivalence retains the entire corner evaluation. -/
theorem restrictedCanonicalBoundary_corner :
    homologyMap (coverRestrictionFunctor.map canonicalBoundaryEquiv.hom) 1 ≫ restrictedCanonicalCorner =
      homologyMap (coverRestrictionFunctor.map fullFaceBoundaryEquiv.inv) 1 ≫ restrictedFullCorner := by
  change homologyMap (coverRestrictionFunctor.map
    ((fullFaceBoundaryEquiv.inv ≫ fullFaceConeParabolicEquiv.hom) ≫ parabolicCanonicalEquiv.hom)) 1 ≫ _ = _
  erw [Category.assoc, Functor.map_comp, homologyMap_comp, Category.assoc,
    restrictedFullFaceCanonical_corner]

/-- The actual canonical boundary model has minus its augmented corner as genuine MV edge.
Every map here is the restriction of the full integral comparison. -/
theorem restrictedCanonicalBoundary_edge :
    homologyMap (coverRestrictionFunctor.map canonicalBoundaryEquiv.hom) 1 ≫ restrictedCanonicalCorner =
      -boundaryEdgeMap := by
  rw [restrictedCanonicalBoundary_corner]
  have h := congrArg (fun t => homologyMap (coverRestrictionFunctor.map fullFaceBoundaryEquiv.inv) 1 ≫ t)
    restrictedFullFace_boundary_edge
  have hi : homologyMap (coverRestrictionFunctor.map fullFaceBoundaryEquiv.inv) 1 ≫
      homologyMap (coverRestrictionFunctor.map fullFaceConeToBoundary) 1 = 𝟙 _ := by
    rw [← fullFaceBoundaryEquiv_hom]
    exact ((Rep.resFunctor principalSix.subtype).mapHomotopyEquiv fullFaceBoundaryEquiv).toHomologyIso 1 |>.inv_hom_id
  erw [← Category.assoc, hi, Category.id_comp, comp_neg] at h
  have hn := congrArg Neg.neg h
  simp only [neg_neg] at hn
  exact hn.symm

/-- An actual canonical cycle maps back to a boundary cycle with edge minus its complete corner augmentation. -/
theorem restrictedCanonicalBoundary_inverse_edge :
    homologyMap (coverRestrictionFunctor.map canonicalBoundaryEquiv.inv) 1 ≫ boundaryEdgeMap =
      -restrictedCanonicalCorner := by
  have h := congrArg (fun t => homologyMap (coverRestrictionFunctor.map canonicalBoundaryEquiv.inv) 1 ≫ t)
    restrictedCanonicalBoundary_edge
  have hi : homologyMap (coverRestrictionFunctor.map canonicalBoundaryEquiv.inv) 1 ≫
      homologyMap (coverRestrictionFunctor.map canonicalBoundaryEquiv.hom) 1 = 𝟙 _ :=
    ((Rep.resFunctor principalSix.subtype).mapHomotopyEquiv canonicalBoundaryEquiv).toHomologyIso 1 |>.inv_hom_id
  erw [← Category.assoc, hi, Category.id_comp, comp_neg] at h
  have hn := congrArg Neg.neg h
  simp only [neg_neg] at hn
  exact hn.symm

end TernaryPoly.OrdinaryBoundaryActualEvaluation
