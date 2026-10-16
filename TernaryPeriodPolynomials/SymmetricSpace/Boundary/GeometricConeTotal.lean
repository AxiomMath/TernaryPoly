module

public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.GeometricConeFaces
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryResolution.Biproduct

@[expose] public section

noncomputable section
namespace TernaryPoly.SymmetricSpaceBoundaryGeometricCone
open CategoryTheory Category Limits HomologicalComplex IntegralGL3Congruence
open SymmetricSpaceBoundaryIncidenceHomology SymmetricSpaceBoundaryFaceAugmentation SymmetricSpaceBoundaryMV
open EquivariantSingularSmall EquivariantSingularResolution SingularLocalCoefficient

instance facesToOpen_quasiIso : QuasiIso facesToOpen :=
  BoundaryFaceResolutionComparison.biprodMap_quasiIso lineToOpen planeToOpen

/-- The full face incidence admits a literal equivariant graded retraction on singular simplices. -/
def faceRetraction (n : ℕ) : (lineChains ⊞ planeChains).X n ⟶ flagChains.X n :=
  (biprod.fst : lineChains ⊞ planeChains ⟶ lineChains).f n ≫
    BoundaryFaceResolutionComparison.degreeRetraction lineFaceMap lineFaceMap_equivariant lineFaceMap_injective n

theorem face_f_r (n : ℕ) : faceArrow.f n ≫ faceRetraction n=𝟙 _ := by
  change faceArrow.f n ≫ ((biprod.fst : lineChains ⊞ planeChains ⟶ lineChains).f n ≫ _)=_
  rw [←Category.assoc]
  change ((biprod.lift lineChainMap (-planeChainMap)).f n ≫
    (biprod.fst : lineChains ⊞ planeChains ⟶ lineChains).f n) ≫ _=_
  rw [biprod_lift_fst_f]
  exact BoundaryFaceResolutionComparison.degreeMap_retraction lineFaceMap lineFaceMap_equivariant lineFaceMap_injective n

/-- The genuine total chain cone of the full line-face, plane-face and flag-corner family. -/
abbrev faceCone := homotopyCofiber faceArrow

/-- The map from the full-face cone to actual small chains is induced by the strict geometric square. -/
def faceConeToSmall : faceCone ⟶ smallComplex :=
  BoundaryFaceResolutionComparison.coneMap faceArrow faceRetraction face_f_r mvComplex flagToOpen facesToOpen faceArrow_square

instance faceConeToSmall_quasiIso : QuasiIso faceConeToSmall :=
  BoundaryFaceResolutionComparison.coneMap_quasiIso faceArrow faceRetraction face_f_r
    mvComplex flagToOpen facesToOpen faceArrow_square mvShortExact flagToOpen_quasiIso facesToOpen_quasiIso

/-- The actual map from the full-face total cone to the entire boundary singular complex. -/
def faceConeToBoundary : faceCone ⟶ boundaryChains := faceConeToSmall ≫ smallEquiv.hom

instance faceConeToBoundary_quasiIso : QuasiIso faceConeToBoundary := by
  unfold faceConeToBoundary
  infer_instance

/-- The full-face comparison retains the two literal geometric face inclusions. -/
theorem faceConeToBoundary_inr : homotopyCofiber.inr faceArrow ≫ faceConeToBoundary=
    facesToOpen ≫ mvComplex.g ≫ smallEquiv.hom :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun m => m ≫ smallEquiv.hom)
      (BoundaryFaceResolutionComparison.coneMap_inr faceArrow faceRetraction face_f_r
        mvComplex flagToOpen facesToOpen faceArrow_square)).trans (Category.assoc _ _ _))

theorem faceMiddle_projective (n : ℕ) : Projective ((lineChains ⊞ planeChains).X n) := by
  have : Projective (lineChains.X n) := lineResolution.projective n
  have : Projective (planeChains.X n) := planeResolution.projective n
  exact Projective.of_iso (HomologicalComplex.biprodXIso lineChains planeChains n).symm inferInstance

theorem faceCone_projective (n : ℕ) : Projective (faceCone.X n) := by
  have : ∀ n, Projective (flagChains.X n) := flagResolution.projective
  have : ∀ n, Projective ((lineChains ⊞ planeChains).X n) := faceMiddle_projective
  exact BoundaryFaceResolutionComparison.projectiveCone faceArrow n

/-- Degreewise projectivity upgrades this actual map to an equivariant chain homotopy equivalence. -/
theorem exists_faceConeBoundaryEquiv : ∃ e : _root_.HomotopyEquiv faceCone boundaryChains,
    e.hom=faceConeToBoundary := by
  have : ∀ n, Projective (faceCone.X n) := faceCone_projective
  have : ∀ n, Projective (boundaryChains.X n) := fun n => chainRep_projective principalSix ambient n
  exact (ChainComplex.quasiIso_iff_of_projective faceConeToBoundary).mp inferInstance

def faceConeBoundaryEquiv : _root_.HomotopyEquiv faceCone boundaryChains :=
  Classical.choose exists_faceConeBoundaryEquiv

theorem faceConeBoundaryEquiv_hom : faceConeBoundaryEquiv.hom=faceConeToBoundary :=
  Classical.choose_spec exists_faceConeBoundaryEquiv

/-- The actual full-family total cochains: face cochains in degree n and corner cochains in degree n-1. -/
abbrev faceTotalCochains (W : Rep.{0} ℚ principalSix) := homCochains faceCone W

/-- Genuine boundary cochains map to the full-family total cone by the actual geometric chain map. -/
def boundaryToFaceTotal (W : Rep.{0} ℚ principalSix) : homCochains boundaryChains W ⟶ faceTotalCochains W :=
  homPullback faceConeToBoundary W

instance boundaryToFaceTotal_quasiIso (W : Rep.{0} ℚ principalSix) : QuasiIso (boundaryToFaceTotal W) := by
  have h := homPullback_quasiIso_of_homotopyEquiv faceConeBoundaryEquiv W
  rw [faceConeBoundaryEquiv_hom] at h
  exact h

/-- The actual geometric local-system boundary cochains compare to the full-face total cone. -/
def localBoundaryToFaceTotal (W : Rep.{0} ℚ principalSix) : localBoundaryCochains W ⟶ faceTotalCochains W :=
  (cochainIso SingularBoundaryRestriction.boundaryProjection SingularBoundaryRestriction.boundaryQuotientCovering W).inv ≫
    boundaryToFaceTotal W

instance localBoundaryToFaceTotal_quasiIso (W : Rep.{0} ℚ principalSix) : QuasiIso (localBoundaryToFaceTotal W) := by
  unfold localBoundaryToFaceTotal
  infer_instance

/-- This comparison is map-compatible with the actual restriction to all full faces. -/
theorem boundaryToFaceTotal_restriction (W : Rep.{0} ℚ principalSix) :
    boundaryToFaceTotal W ≫ homPullback (homotopyCofiber.inr faceArrow) W=
      homPullback (facesToOpen ≫ mvComplex.g ≫ smallEquiv.hom) W :=
  (homPullback_comp _ _ W).symm.trans (congrArg (fun m => homPullback m W) faceConeToBoundary_inr)

end TernaryPoly.SymmetricSpaceBoundaryGeometricCone
