module

public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.FullConeMap
public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.FullCofiberNaturality

@[expose] public section

noncomputable section
namespace TernaryPoly.SymmetricSpaceBoundaryFull
open CategoryTheory Category Limits HomologicalComplex IntegralGL3Congruence
open SymmetricSpaceBoundaryFullTransfer

abbrev coverFacesBoundary :=
  biprod.desc SymmetricSpaceBoundaryGeometricCone.lineChainToBoundary
    SymmetricSpaceBoundaryGeometricCone.planeChainToBoundary

theorem facesBoundary_restriction : faceMiddleRestrictionIso.inv ≫
    coverRestrictionFunctor.map fullFacesToBoundary = coverFacesBoundary :=
  biprod.mapBiprod_inv_map_desc coverRestrictionFunctor fullLineChains fullPlaneChains
    fullLineChainToBoundary fullPlaneChainToBoundary

theorem restrictedFace_boundary_zero : SymmetricSpaceBoundaryGeometricCone.faceArrow ≫
    (faceMiddleRestrictionIso.inv ≫ coverRestrictionFunctor.map fullFacesToBoundary) = 0 := by
  have hc : (coverRestrictionFunctor.map fullFaceArrow ≫ faceMiddleRestrictionIso.hom) ≫
      (faceMiddleRestrictionIso.inv ≫ coverRestrictionFunctor.map fullFacesToBoundary) = 0 := by
    rw [Category.assoc,Iso.hom_inv_id_assoc]
    exact (coverRestrictionFunctor.map_comp _ _).symm.trans
      ((congrArg coverRestrictionFunctor.map fullFace_boundary_zero).trans (coverRestrictionFunctor.map_zero _ _))
  exact (congrArg (fun m => m ≫ (faceMiddleRestrictionIso.inv ≫
    coverRestrictionFunctor.map fullFacesToBoundary)) faceArrow_restriction.symm).trans hc

def coverStrictConeToBoundary : SymmetricSpaceBoundaryGeometricCone.faceCone ⟶
    SymmetricSpaceBoundaryIncidenceHomology.boundaryChains :=
  homotopyCofiber.desc SymmetricSpaceBoundaryGeometricCone.faceArrow
    (faceMiddleRestrictionIso.inv ≫ coverRestrictionFunctor.map fullFacesToBoundary)
    (Homotopy.ofEq restrictedFace_boundary_zero)

/-- The full cone projection restricts to the literal signed cone projection on the cover. -/
theorem fullConeMap_restriction : faceConeRestrictionIso.inv ≫
    coverRestrictionFunctor.map fullFaceConeToBoundary = coverStrictConeToBoundary := by
  let α : Arrow.mk (coverRestrictionFunctor.map fullFaceArrow) ≅
      Arrow.mk SymmetricSpaceBoundaryGeometricCone.faceArrow :=
    Arrow.isoMk (Iso.refl _) faceMiddleRestrictionIso (by
      change 𝟙 _ ≫ SymmetricSpaceBoundaryGeometricCone.faceArrow = _
      rw [Category.id_comp]
      exact faceArrow_restriction.symm)
  have hm : coverRestrictionFunctor.map fullFaceArrow ≫ coverRestrictionFunctor.map fullFacesToBoundary = 0 := by
    rw [← Functor.map_comp,fullFace_boundary_zero,Functor.map_zero]
  change (homotopyCofiber.mapArrowHom SymmetricSpaceBoundaryGeometricCone.faceArrow
      (coverRestrictionFunctor.map fullFaceArrow) (fun n => ⟨n+1,Cofiber.down n⟩) α.inv ≫
    (homotopyCofiber.mapHomologicalComplexObjIso fullFaceArrow (Rep.resFunctor principalSix.subtype)).inv) ≫
      coverRestrictionFunctor.map (homotopyCofiber.desc fullFaceArrow fullFacesToBoundary (Homotopy.ofEq fullFace_boundary_zero)) = _
  rw [Category.assoc]
  exact (congrArg (fun m => homotopyCofiber.mapArrowHom SymmetricSpaceBoundaryGeometricCone.faceArrow
      (coverRestrictionFunctor.map fullFaceArrow) (fun n => ⟨n+1,Cofiber.down n⟩) α.inv ≫ m)
      (Cofiber.map_desc fullFaceArrow fullFacesToBoundary fullFace_boundary_zero (Rep.resFunctor principalSix.subtype))).trans
    (Cofiber.map_arrow_desc SymmetricSpaceBoundaryGeometricCone.faceArrow
      (coverRestrictionFunctor.map fullFaceArrow) α.inv (coverRestrictionFunctor.map fullFacesToBoundary) hm)

/-- The geometric comparison vanishes on the shifted corner inclusion. -/
theorem frozenConeMap_inl (n : ℕ) :
    homotopyCofiber.inlX SymmetricSpaceBoundaryGeometricCone.faceArrow n (n+1) (Cofiber.down n) ≫
      SymmetricSpaceBoundaryGeometricCone.faceConeToBoundary.f (n+1) = 0 := by
  let p := BoundaryFaceResolutionComparison.Cone.projection
    (ShortComplex.cokernelSequence SymmetricSpaceBoundaryGeometricCone.faceArrow)
  let q := BoundaryFaceResolutionComparison.quotientMap SymmetricSpaceBoundaryGeometricCone.faceArrow
    SymmetricSpaceBoundaryIncidenceHomology.mvComplex SymmetricSpaceBoundaryGeometricCone.flagToOpen
    SymmetricSpaceBoundaryGeometricCone.facesToOpen SymmetricSpaceBoundaryGeometricCone.faceArrow_square
  let u := homotopyCofiber.inlX SymmetricSpaceBoundaryGeometricCone.faceArrow n (n+1) (Cofiber.down n)
  have hp : u ≫ p.f (n+1) = 0 :=
    BoundaryFaceResolutionComparison.Cone.left_projection_f
      (ShortComplex.cokernelSequence SymmetricSpaceBoundaryGeometricCone.faceArrow) n (n+1) (Cofiber.down n)
  have hq : u ≫ (p.f (n+1) ≫ q.f (n+1)) = 0 :=
    (Category.assoc _ _ _).symm.trans ((congrArg (fun m => m ≫ q.f (n+1)) hp).trans zero_comp)
  exact (Category.assoc u (p.f (n+1) ≫ q.f (n+1))
    (SymmetricSpaceBoundaryIncidenceHomology.smallEquiv.hom.f (n+1))).symm.trans
      ((congrArg (fun m => m ≫ SymmetricSpaceBoundaryIncidenceHomology.smallEquiv.hom.f (n+1)) hq).trans zero_comp)

/-- Exact source-matched identification with the whole-boundary cone map. -/
theorem coverStrictConeToBoundary_eq :
    coverStrictConeToBoundary = SymmetricSpaceBoundaryGeometricCone.faceConeToBoundary := by
  have hr : homotopyCofiber.inr SymmetricSpaceBoundaryGeometricCone.faceArrow ≫
      SymmetricSpaceBoundaryGeometricCone.faceConeToBoundary = coverFacesBoundary :=
    SymmetricSpaceBoundaryGeometricCone.faceConeToBoundary_inr.trans
      SymmetricSpaceBoundaryGeometricCone.fullFace_boundary_map
  apply HomologicalComplex.hom_ext
  intro n
  cases n with
  | zero =>
    apply homotopyCofiber.ext_from_X' SymmetricSpaceBoundaryGeometricCone.faceArrow 0
      (by simp [ComplexShape.down_Rel])
    exact ((homotopyCofiber.inrX_desc_f _ _ _ 0).trans
      (congrArg (fun m => m.f 0) facesBoundary_restriction)).trans
        (congrArg (fun m => m.f 0) hr).symm
  | succ n =>
    apply homotopyCofiber.ext_from_X SymmetricSpaceBoundaryGeometricCone.faceArrow n (n+1) (Cofiber.down n)
    · exact (homotopyCofiber.inlX_desc_f _ _ _ n (n+1) (Cofiber.down n)).trans (frozenConeMap_inl n).symm
    · exact ((homotopyCofiber.inrX_desc_f _ _ _ (n+1)).trans
        (congrArg (fun m => m.f (n+1)) facesBoundary_restriction)).trans
          (congrArg (fun m => m.f (n+1)) hr).symm

end TernaryPoly.SymmetricSpaceBoundaryFull
