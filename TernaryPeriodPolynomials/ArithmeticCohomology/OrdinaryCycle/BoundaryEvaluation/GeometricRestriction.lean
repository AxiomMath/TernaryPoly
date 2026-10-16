module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.BoundaryEvaluation.GeometricEdge
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.BoundaryEvaluation.RestrictionConeCorner
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.BoundaryEvaluation.CanonicalCorner

@[expose] public section


noncomputable section
namespace TernaryPoly.OrdinaryBoundaryActualEvaluation
open CategoryTheory Limits HomologicalComplex BoundaryFaceResolutionComparison
open IntegralGL3Congruence SymmetricSpaceBoundaryFullTransfer SymmetricSpaceBoundaryFull
open SymmetricSpaceBoundaryFaceAugmentation SymmetricSpaceBoundaryGeometricCone

/-- The full integral geometric augmentation restricts to the literal flag augmentation. -/
theorem fullFlagAugmentation_restriction :
    (Rep.resFunctor principalSix.subtype).map (fullFlagResolution.π.f 0) = flagAugmentation := rfl

/-- The actual restriction of the complete full geometric corner cochain. -/
def restrictedFullCorner : (restrictedComplex principalSix fullFaceCone).homology 1 ⟶ flagLabels :=
  restrictedEvaluation principalSix fullFaceCone fullFlagLabels 1
    (coneCornerCochain fullFaceArrow fullFlagLabels (fullFlagResolution.π.f 0))
    (coneCornerCochain_boundary fullFaceArrow fullFlagLabels (fullFlagResolution.π.f 0)
      fullFlagResolution.complex_d_comp_π_f_zero)

/-- Restriction of the full cone's corner is the exact actual geometric corner, at chain level. -/
theorem fullFaceConeRestriction_cornerCochain :
    faceConeRestrictionIso.inv.f 1 ≫ (Rep.resFunctor principalSix.subtype).map
      (coneCornerCochain fullFaceArrow fullFlagLabels (fullFlagResolution.π.f 0)) =
        coneCornerCochain faceArrow flagLabels flagAugmentation := by
  let α : Arrow.mk (coverRestrictionFunctor.map fullFaceArrow) ≅ Arrow.mk faceArrow :=
    Arrow.isoMk (Iso.refl _) faceMiddleRestrictionIso (by
      change 𝟙 _ ≫ faceArrow = _
      rw [Category.id_comp]
      exact faceArrow_restriction.symm)
  change ((homotopyCofiber.mapArrowHom faceArrow (coverRestrictionFunctor.map fullFaceArrow)
    (fun n => ⟨n+1,Cone.downRel n⟩) α.inv).f 1 ≫
      (homotopyCofiber.mapHomologicalComplexObjIso fullFaceArrow
        (Rep.resFunctor principalSix.subtype)).inv.f 1) ≫ _ = _
  erw [Category.assoc, coneRestriction_cornerCochain, coneArrow_cornerCochain]
  change coneCornerCochain faceArrow flagLabels
    ((𝟙 _) ≫ (Rep.resFunctor principalSix.subtype).map (fullFlagResolution.π.f 0)) = _
  erw [Category.id_comp, fullFlagAugmentation_restriction]

/-- The restriction/cofiber comparison retains the actual homology corner evaluator. -/
theorem fullFaceConeRestriction_corner :
    homologyMap faceConeRestrictionIso.inv 1 ≫ restrictedFullCorner = geometricCornerHomology := by
  apply evaluationOfCochain_natural
  exact fullFaceConeRestriction_cornerCochain

/-- The full integral face-cone map restricts to the actual geometric boundary edge, with its minus sign. -/
theorem restrictedFullFace_boundary_edge :
    homologyMap (coverRestrictionFunctor.map fullFaceConeToBoundary) 1 ≫
      SymmetricSpaceBoundaryIncidenceHomology.boundaryEdgeMap = -restrictedFullCorner := by
  apply (cancel_epi (homologyMap faceConeRestrictionIso.inv 1)).mp
  erw [← Category.assoc, ← homologyMap_comp,
    fullConeMap_restriction, coverStrictConeToBoundary_eq, geometricCone_boundary_edge,
    Preadditive.comp_neg, fullFaceConeRestriction_corner]

end TernaryPoly.OrdinaryBoundaryActualEvaluation
