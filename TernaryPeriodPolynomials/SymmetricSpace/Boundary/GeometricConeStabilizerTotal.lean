module

public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.GeometricConeStabilizers
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryResolution.CofiberMap

@[expose] public section

noncomputable section
namespace TernaryPoly.SymmetricSpaceBoundaryGeometricCone
open CategoryTheory Category Limits HomologicalComplex Preadditive
open IntegralGL3Congruence SymmetricSpaceBoundaryFaceAugmentation
open BoundaryFaceResolutionComparison EquivariantSingularSmall

section Generic
variable {C : Type*} [Category* C] [Abelian C]
  {F L P F' L' P' : ChainComplex C ℕ}
  (a : F ⟶ L) (b : F ⟶ P) (a' : F' ⟶ L') (b' : F' ⟶ P')
  (u : F ⟶ F') (v : L ⟶ L') (w : P ⟶ P')

/-- The line and plane homotopies assemble with the literal incidence sign. -/
def signedSquareHomotopy (ha : Homotopy (a ≫ v) (u ≫ a')) (hb : Homotopy (b ≫ w) (u ≫ b')) :
    Homotopy (biprod.lift a (-b) ≫ biprod.map v w) (u ≫ biprod.lift a' (-b')) := by
  have h := (ha.compRight biprod.inl).add (hb.compRight (-biprod.inr))
  simpa only [biprod.lift_eq,Category.assoc,comp_add,add_comp,comp_neg,neg_comp,
    biprod.inl_map,biprod.inr_map] using h
end Generic

/-- The full-family stabilizer chain incidence retains line minus plane. -/
def stabilizerFaceArrow : flagStabilizerModel.complex ⟶ lineStabilizerModel.complex ⊞ planeStabilizerModel.complex :=
  biprod.lift lineStabilizerArrow (-planeStabilizerArrow)

def stabilizerMiddleComparison : lineChains ⊞ planeChains ⟶
    lineStabilizerModel.complex ⊞ planeStabilizerModel.complex :=
  biprod.map lineStabilizerComparison.hom planeStabilizerComparison.hom

instance stabilizerMiddleComparison_quasiIso : QuasiIso stabilizerMiddleComparison :=
  biprodMap_quasiIso lineStabilizerComparison.hom planeStabilizerComparison.hom

theorem stabilizerMiddle_projective (n : ℕ) :
    Projective ((lineStabilizerModel.complex ⊞ planeStabilizerModel.complex).X n) :=
  Projective.of_iso (HomologicalComplex.biprodXIso lineStabilizerModel.complex planeStabilizerModel.complex n).symm
    inferInstance

theorem exists_stabilizerMiddleEquiv : ∃ e : _root_.HomotopyEquiv (lineChains ⊞ planeChains)
    (lineStabilizerModel.complex ⊞ planeStabilizerModel.complex), e.hom=stabilizerMiddleComparison := by
  have : ∀ n, Projective ((lineChains ⊞ planeChains).X n) := faceMiddle_projective
  have : ∀ n, Projective ((lineStabilizerModel.complex ⊞ planeStabilizerModel.complex).X n) := stabilizerMiddle_projective
  exact (ChainComplex.quasiIso_iff_of_projective stabilizerMiddleComparison).mp inferInstance

def stabilizerMiddleEquiv := Classical.choose exists_stabilizerMiddleEquiv

def stabilizerFaceSquare : Homotopy (faceArrow ≫ stabilizerMiddleComparison)
    (flagStabilizerComparison.hom ≫ stabilizerFaceArrow) :=
  signedSquareHomotopy _ _ _ _ _ _ _
    (comparisonHomotopy flagResolution flagStabilizerModel lineResolution lineStabilizerModel lineIncidence lineResolutionMap)
    (comparisonHomotopy flagResolution flagStabilizerModel planeResolution planeStabilizerModel planeIncidence planeResolutionMap)

abbrev stabilizerFaceCone := homotopyCofiber stabilizerFaceArrow

/-- The explicit homotopy-square cone map retains all specified component comparisons. -/
def faceConeToStabilizer : faceCone ⟶ stabilizerFaceCone :=
  CofiberSequence.comparisonMap faceArrow stabilizerFaceArrow flagStabilizerComparison.hom
    stabilizerMiddleComparison stabilizerFaceSquare

instance faceConeToStabilizer_quasiIso : QuasiIso faceConeToStabilizer :=
  CofiberSequence.comparisonMap_quasiIso _ _ _ _ _ flagStabilizerComparison rfl
    stabilizerMiddleEquiv (Classical.choose_spec exists_stabilizerMiddleEquiv)

theorem faceConeToStabilizer_inr : homotopyCofiber.inr faceArrow ≫ faceConeToStabilizer=
    stabilizerMiddleComparison ≫ homotopyCofiber.inr stabilizerFaceArrow :=
  CofiberSequence.inr_comparisonMap _ _ _ _ _

theorem stabilizerFaceCone_projective (n : ℕ) : Projective (stabilizerFaceCone.X n) := by
  have : ∀ n, Projective (flagStabilizerModel.complex.X n) := flagStabilizerModel.projective
  have : ∀ n, Projective ((lineStabilizerModel.complex ⊞ planeStabilizerModel.complex).X n) := stabilizerMiddle_projective
  exact projectiveCone stabilizerFaceArrow n

theorem exists_faceConeStabilizerEquiv : ∃ e : _root_.HomotopyEquiv faceCone stabilizerFaceCone,
    e.hom=faceConeToStabilizer := by
  have : ∀ n, Projective (faceCone.X n) := faceCone_projective
  have : ∀ n, Projective (stabilizerFaceCone.X n) := stabilizerFaceCone_projective
  exact (ChainComplex.quasiIso_iff_of_projective faceConeToStabilizer).mp inferInstance

def faceConeStabilizerEquiv := Classical.choose exists_faceConeStabilizerEquiv

theorem faceConeStabilizerEquiv_hom : faceConeStabilizerEquiv.hom=faceConeToStabilizer :=
  Classical.choose_spec exists_faceConeStabilizerEquiv

/-- The total induced-stabilizer cochains. Their components are the full Shapiro products. -/
abbrev stabilizerTotalCochains (W : Rep.{0} ℚ principalSix) := homCochains stabilizerFaceCone W

def stabilizerTotalToGeometric (W : Rep.{0} ℚ principalSix) :
    stabilizerTotalCochains W ⟶ faceTotalCochains W := homPullback faceConeToStabilizer W

instance stabilizerTotalToGeometric_quasiIso (W : Rep.{0} ℚ principalSix) :
    QuasiIso (stabilizerTotalToGeometric W) := by
  have h := homPullback_quasiIso_of_homotopyEquiv faceConeStabilizerEquiv W
  rw [faceConeStabilizerEquiv_hom] at h
  exact h

/-- An actual quasi-isomorphism from genuine boundary local-system cochains to the stabilizer total model. -/
def localBoundaryToStabilizerTotal (W : Rep.{0} ℚ principalSix) :
    localBoundaryCochains W ⟶ stabilizerTotalCochains W :=
  localBoundaryToFaceTotal W ≫ homPullback faceConeStabilizerEquiv.inv W

instance localBoundaryToStabilizerTotal_quasiIso (W : Rep.{0} ℚ principalSix) :
    QuasiIso (localBoundaryToStabilizerTotal W) := by
  have : QuasiIso (homPullback faceConeStabilizerEquiv.inv W) :=
    homPullback_quasiIso_of_homotopyEquiv faceConeStabilizerEquiv.symm W
  exact _root_.quasiIso_comp (localBoundaryToFaceTotal W) (homPullback faceConeStabilizerEquiv.inv W)

/-- The forward total comparison preserves the specified middle-face maps exactly. -/
theorem stabilizerTotalToGeometric_restriction (W : Rep.{0} ℚ principalSix) :
    stabilizerTotalToGeometric W ≫ homPullback (homotopyCofiber.inr faceArrow) W=
      homPullback (homotopyCofiber.inr stabilizerFaceArrow) W ≫ homPullback stabilizerMiddleComparison W := by
  exact (homPullback_comp (homotopyCofiber.inr faceArrow) faceConeToStabilizer W).symm.trans
    ((congrArg (fun f => homPullback f W) faceConeToStabilizer_inr).trans
      (homPullback_comp stabilizerMiddleComparison (homotopyCofiber.inr stabilizerFaceArrow) W))

end TernaryPoly.SymmetricSpaceBoundaryGeometricCone
