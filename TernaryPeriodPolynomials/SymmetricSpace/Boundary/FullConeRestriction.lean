module

public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.FullIncidence

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceBoundaryFull
open CategoryTheory Limits HomologicalComplex IntegralGL3Congruence
open SymmetricSpaceBoundaryFullTransfer

abbrev coverRestrictionFunctor : ChainComplex (Rep ℚ ModThreeGoodAction.IntegralGL) ℕ ⥤
    ChainComplex (Rep ℚ principalSix) ℕ := (Rep.resFunctor principalSix.subtype).mapHomologicalComplex (ComplexShape.down ℕ)

instance coverRestriction_preservesBinaryBiproducts : PreservesBinaryBiproducts coverRestrictionFunctor :=
  preservesBinaryBiproducts_of_preservesBinaryProducts _

/-- Restriction preserves the actual line/plane biproduct through its canonical comparison. -/
def faceMiddleRestrictionIso : restrictedComplex principalSix (fullLineChains ⊞ fullPlaneChains) ≅
    SymmetricSpaceBoundaryFaceAugmentation.lineChains ⊞ SymmetricSpaceBoundaryFaceAugmentation.planeChains :=
  coverRestrictionFunctor.mapBiprod fullLineChains fullPlaneChains

theorem faceArrow_restriction :
    coverRestrictionFunctor.map fullFaceArrow ≫ faceMiddleRestrictionIso.hom =
      SymmetricSpaceBoundaryGeometricCone.faceArrow := by
  have h := biprod.map_lift_mapBiprod coverRestrictionFunctor fullLineChains fullPlaneChains
    fullLineChainMap (-fullPlaneChainMap)
  exact h.trans (congrArg
    (fun m => biprod.lift (coverRestrictionFunctor.map fullLineChainMap) m)
    (coverRestrictionFunctor.map_neg (f := fullPlaneChainMap)))

/-- Restriction of the full geometric cone recovers the actual cover cone. -/
def faceConeRestrictionIso : restrictedComplex principalSix fullFaceCone ≅
    SymmetricSpaceBoundaryGeometricCone.faceCone :=
  homotopyCofiber.mapHomologicalComplexObjIso fullFaceArrow (Rep.resFunctor principalSix.subtype) ≪≫
    homotopyCofiber.mapArrowIso _ _ (fun n => ⟨n+1,rfl⟩)
      (Arrow.isoMk (Iso.refl _) faceMiddleRestrictionIso (by
        change 𝟙 _ ≫ SymmetricSpaceBoundaryGeometricCone.faceArrow = _
        rw [Category.id_comp]
        exact faceArrow_restriction.symm))

end TernaryPoly.SymmetricSpaceBoundaryFull
