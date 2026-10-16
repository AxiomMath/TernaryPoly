module

public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.FullParabolicModels

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceBoundaryFull
open CategoryTheory Category Limits HomologicalComplex Preadditive
open BoundaryFaceResolutionComparison EquivariantSingularSmall

theorem fullFaceMiddle_projective (n : ℕ) : Projective ((fullLineChains ⊞ fullPlaneChains).X n) :=
  Projective.of_iso (HomologicalComplex.biprodXIso fullLineChains fullPlaneChains n).symm inferInstance

theorem fullFaceCone_projective (n : ℕ) : Projective (fullFaceCone.X n) := by
  have : ∀ n, Projective ((fullLineChains ⊞ fullPlaneChains).X n) := fullFaceMiddle_projective
  exact projectiveCone fullFaceArrow n

abbrev fullFaceTotalCochains (W : Rep.{0} ℚ ModThreeGoodAction.IntegralGL) := homCochains fullFaceCone W

/-- The full-family stabilizer chain incidence retains line minus plane. -/
def parabolicFaceArrow : flagParabolicResolution.complex ⟶ lineParabolicResolution.complex ⊞ planeParabolicResolution.complex :=
  biprod.lift parabolicLineArrow (-parabolicPlaneArrow)

def parabolicMiddleComparison : fullLineChains ⊞ fullPlaneChains ⟶
    lineParabolicResolution.complex ⊞ planeParabolicResolution.complex :=
  biprod.map lineParabolicComparison.hom planeParabolicComparison.hom

instance parabolicMiddleComparison_quasiIso : QuasiIso parabolicMiddleComparison :=
  biprodMap_quasiIso lineParabolicComparison.hom planeParabolicComparison.hom

theorem parabolicMiddle_projective (n : ℕ) :
    Projective ((lineParabolicResolution.complex ⊞ planeParabolicResolution.complex).X n) :=
  Projective.of_iso (HomologicalComplex.biprodXIso lineParabolicResolution.complex planeParabolicResolution.complex n).symm
    inferInstance

theorem exists_parabolicMiddleEquiv : ∃ e : _root_.HomotopyEquiv (fullLineChains ⊞ fullPlaneChains)
    (lineParabolicResolution.complex ⊞ planeParabolicResolution.complex), e.hom=parabolicMiddleComparison := by
  have : ∀ n, Projective ((fullLineChains ⊞ fullPlaneChains).X n) := fullFaceMiddle_projective
  have : ∀ n, Projective ((lineParabolicResolution.complex ⊞ planeParabolicResolution.complex).X n) := parabolicMiddle_projective
  exact (ChainComplex.quasiIso_iff_of_projective parabolicMiddleComparison).mp inferInstance

def parabolicMiddleEquiv := Classical.choose exists_parabolicMiddleEquiv

def parabolicFaceSquare : Homotopy (fullFaceArrow ≫ parabolicMiddleComparison)
    (flagParabolicComparison.hom ≫ parabolicFaceArrow) :=
  SymmetricSpaceBoundaryGeometricCone.signedSquareHomotopy _ _ _ _ _ _ _
    (comparisonHomotopy fullFlagResolution flagParabolicResolution fullLineResolution lineParabolicResolution fullLineIncidence fullLineResolutionMap)
    (comparisonHomotopy fullFlagResolution flagParabolicResolution fullPlaneResolution planeParabolicResolution fullPlaneIncidence fullPlaneResolutionMap)

abbrev parabolicFaceCone := homotopyCofiber parabolicFaceArrow

/-- The explicit homotopy-square cone map retains all specified component comparisons. -/
def fullFaceConeToParabolic : fullFaceCone ⟶ parabolicFaceCone :=
  CofiberSequence.comparisonMap fullFaceArrow parabolicFaceArrow flagParabolicComparison.hom
    parabolicMiddleComparison parabolicFaceSquare

instance fullFaceConeToParabolic_quasiIso : QuasiIso fullFaceConeToParabolic :=
  CofiberSequence.comparisonMap_quasiIso _ _ _ _ _ flagParabolicComparison rfl
    parabolicMiddleEquiv (Classical.choose_spec exists_parabolicMiddleEquiv)

theorem fullFaceConeToParabolic_inr : homotopyCofiber.inr fullFaceArrow ≫ fullFaceConeToParabolic=
    parabolicMiddleComparison ≫ homotopyCofiber.inr parabolicFaceArrow :=
  CofiberSequence.inr_comparisonMap _ _ _ _ _

theorem parabolicFaceCone_projective (n : ℕ) : Projective (parabolicFaceCone.X n) := by
  have : ∀ n, Projective (flagParabolicResolution.complex.X n) := flagParabolicResolution.projective
  have : ∀ n, Projective ((lineParabolicResolution.complex ⊞ planeParabolicResolution.complex).X n) := parabolicMiddle_projective
  exact projectiveCone parabolicFaceArrow n

theorem exists_fullFaceConeParabolicEquiv : ∃ e : _root_.HomotopyEquiv fullFaceCone parabolicFaceCone,
    e.hom=fullFaceConeToParabolic := by
  have : ∀ n, Projective (fullFaceCone.X n) := fullFaceCone_projective
  have : ∀ n, Projective (parabolicFaceCone.X n) := parabolicFaceCone_projective
  exact (ChainComplex.quasiIso_iff_of_projective fullFaceConeToParabolic).mp inferInstance

def fullFaceConeParabolicEquiv := Classical.choose exists_fullFaceConeParabolicEquiv

theorem fullFaceConeParabolicEquiv_hom : fullFaceConeParabolicEquiv.hom=fullFaceConeToParabolic :=
  Classical.choose_spec exists_fullFaceConeParabolicEquiv

/-- The total induced-stabilizer cochains. Their components are the full Shapiro products. -/
abbrev parabolicTotalCochains (W : Rep.{0} ℚ ModThreeGoodAction.IntegralGL) := homCochains parabolicFaceCone W

def parabolicTotalToGeometric (W : Rep.{0} ℚ ModThreeGoodAction.IntegralGL) :
    parabolicTotalCochains W ⟶ fullFaceTotalCochains W := homPullback fullFaceConeToParabolic W

instance parabolicTotalToGeometric_quasiIso (W : Rep.{0} ℚ ModThreeGoodAction.IntegralGL) :
    QuasiIso (parabolicTotalToGeometric W) := by
  have h := homPullback_quasiIso_of_homotopyEquiv fullFaceConeParabolicEquiv W
  rw [fullFaceConeParabolicEquiv_hom] at h
  exact h


end TernaryPoly.SymmetricSpaceBoundaryFull
