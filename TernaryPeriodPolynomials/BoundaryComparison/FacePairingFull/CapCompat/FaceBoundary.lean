module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.CapCompat.FaceCone
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.CapCompat.Push.ConeMap
public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.GeometricConeComplete

@[expose] public section


/-!
# `faceConeToBoundary` is strictly compatible with the Alexander-Whitney diagonals

The library's quasi-isomorphism `faceConeToBoundary : faceCone ⟶ boundaryChains` kills the shifted corner coordinate and
restricts to the chain maps induced by the inclusions of the line and plane faces in the boundary; hence it is
strictly compatible with the diagonal of the face cone and the Alexander-Whitney diagonal of the singular chains of
the boundary (`faceConeToBoundary_strict`).  Consequently the cap product commutes with it on the nose.

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory Limits MonoidalCategory
open TernaryPoly TernaryPoly.SymmetricSpaceBoundaryFaceAugmentation
open TernaryPoly.SymmetricSpaceBoundaryGeometricCone
open TernaryPoly.SymmetricSpaceBoundaryIncidenceHomology (boundaryChains ambient)
open TernaryPoly.OrdinaryIncidence TernaryPoly.SymmetricSpaceRationalGluing
  TernaryPoly.SymmetricSpaceBoundaryFaces TernaryPoly.SymmetricSpaceBoundaryMV
  TernaryPoly.SingularBoundaryRestriction TernaryPoly.IntegralGL3Congruence
open TernaryPeriodPolynomials.Argument.TopHomology

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat

open TernaryPoly.BoundaryFaceResolutionComparison in
theorem faceConeToBoundary_f (n : ℕ) : faceConeToBoundary.f n =
    (Cone.projection (ShortComplex.cokernelSequence faceArrow)).f n ≫
      (quotientMap faceArrow SymmetricSpaceBoundaryIncidenceHomology.mvComplex
        flagToOpen facesToOpen faceArrow_square).f n ≫
      SymmetricSpaceBoundaryIncidenceHomology.smallEquiv.hom.f n := rfl

open TernaryPoly.BoundaryFaceResolutionComparison in
theorem faceConeToBoundary_iA (n : ℕ) :
    (pushConeOfCofiber lineChainMap planeChainMap).iA n ≫ faceConeToBoundary.f (n+1) = 0 := by
  have h0 := Cone.left_projection_f (ShortComplex.cokernelSequence faceArrow) n (n+1) rfl
  exact (congrArg (fun m => coneIA lineChainMap planeChainMap n ≫ m) (faceConeToBoundary_f (n+1))).trans
    (((Category.assoc _ _ _).symm.trans (congrArg (fun m => m ≫ _) h0)).trans zero_comp)

theorem faceConeToBoundary_iL (n : ℕ) :
    (pushConeOfCofiber lineChainMap planeChainMap).iL n ≫ faceConeToBoundary.f n =
      lineChainToBoundary.f n := by
  have h := congrArg (fun m => m.f n) (faceConeToBoundary_inr.trans fullFace_boundary_map)
  change HomologicalComplex.homotopyCofiber.inrX faceArrow n ≫ faceConeToBoundary.f n =
    (biprod.desc lineChainToBoundary planeChainToBoundary).f n at h
  change ((biprod.inl : lineChains ⟶ lineChains ⊞ planeChains).f n ≫
    HomologicalComplex.homotopyCofiber.inrX faceArrow n) ≫ faceConeToBoundary.f n = _
  rw [Category.assoc, h, ← HomologicalComplex.comp_f, biprod.inl_desc]

theorem faceConeToBoundary_iP (n : ℕ) :
    (pushConeOfCofiber lineChainMap planeChainMap).iP n ≫ faceConeToBoundary.f n =
      planeChainToBoundary.f n := by
  have h := congrArg (fun m => m.f n) (faceConeToBoundary_inr.trans fullFace_boundary_map)
  change HomologicalComplex.homotopyCofiber.inrX faceArrow n ≫ faceConeToBoundary.f n =
    (biprod.desc lineChainToBoundary planeChainToBoundary).f n at h
  change ((biprod.inr : planeChains ⟶ lineChains ⊞ planeChains).f n ≫
    HomologicalComplex.homotopyCofiber.inrX faceArrow n) ≫ faceConeToBoundary.f n = _
  rw [Category.assoc, h, ← HomologicalComplex.comp_f, biprod.inr_desc]

/-- `faceConeToBoundary` is strictly compatible with the Alexander-Whitney diagonals. -/
theorem faceConeToBoundary_strict (p q n : ℕ) (h : p + q = n) :
    faceConeToBoundary.f n ≫ (singDiagSystem (G := principalSix) (TopCat.of ambient)).Δ p q n h =
      (pushConeOfCofiber lineChainMap planeChainMap).Δ FaceCone.SA FaceCone.SL FaceCone.SP p q n h ≫
        (faceConeToBoundary.f p ⊗ₘ faceConeToBoundary.f q) :=
  PushCone.map_strict (pushConeOfCofiber lineChainMap planeChainMap) FaceCone.SA FaceCone.SL FaceCone.SP
    (singDiagSystem (G := principalSix) (TopCat.of ambient)) faceConeToBoundary lineChainToBoundary
    planeChainToBoundary faceConeToBoundary_iA faceConeToBoundary_iL faceConeToBoundary_iP
    (fun p q n h => singDiag_natural (TopCat.of LineFaceSum) lineToBoundary lineToBoundary_equivariant p q n h)
    (fun p q n h => singDiag_natural (TopCat.of PlaneFaceSum) planeToBoundary planeToBoundary_equivariant p q n h)
    p q n h

end TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat
