module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.BoundaryEvaluation.ConeCorner
public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.FullCanonicalCone

@[expose] public section


noncomputable section
namespace TernaryPoly.OrdinaryBoundaryActualEvaluation
open CategoryTheory Limits HomologicalComplex BoundaryFaceResolutionComparison
open SymmetricSpaceBoundaryFull

/-- The literal full geometric flag augmentation followed by the shifted cone coordinate. -/
def fullGeometricCorner : fullFaceCone.homology 1 ⟶ fullFlagLabels :=
  coneCornerHomology fullFaceArrow fullFlagLabels (fullFlagResolution.π.f 0)
    fullFlagResolution.complex_d_comp_π_f_zero

/-- The complete induced-bar flag augmentation in the intermediate parabolic cone. -/
def parabolicCorner : parabolicFaceCone.homology 1 ⟶ fullFlagLabels :=
  coneCornerHomology parabolicFaceArrow fullFlagLabels (flagParabolicResolution.π.f 0)
    flagParabolicResolution.complex_d_comp_π_f_zero

/-- The complete induced-bar flag augmentation in the literal canonical P/Q/B cone. -/
def canonicalCorner : canonicalFaceCone.homology 1 ⟶ fullFlagLabels :=
  coneCornerHomology canonicalFaceArrow fullFlagLabels (flagParabolicResolution.π.f 0)
    flagParabolicResolution.complex_d_comp_π_f_zero

/-- The actual geometric-to-parabolic flag map preserves its entire augmentation. -/
theorem fullFlagParabolic_augmentation :
    flagParabolicComparison.hom.f 0 ≫ flagParabolicResolution.π.f 0 = fullFlagResolution.π.f 0 :=
  HomologicalComplex.congr_hom (comparison_augmentation fullFlagResolution flagParabolicResolution) 0

/-- The actual parabolic comparison preserves the literal augmented shifted corner. -/
theorem fullFaceConeToParabolic_corner :
    homologyMap fullFaceConeToParabolic 1 ≫ parabolicCorner = fullGeometricCorner :=
  coneComparison_cornerHomology fullFaceArrow fullFlagLabels (fullFlagResolution.π.f 0)
    fullFlagResolution.complex_d_comp_π_f_zero parabolicFaceArrow flagParabolicComparison.hom
    parabolicMiddleComparison parabolicFaceSquare (flagParabolicResolution.π.f 0)
    flagParabolicResolution.complex_d_comp_π_f_zero fullFlagParabolic_augmentation

/-- Replacing lifted parabolic arrows with literal subgroup inclusions preserves the corner exactly. -/
theorem parabolicToCanonical_corner :
    homologyMap parabolicToCanonical 1 ≫ canonicalCorner = parabolicCorner :=
  coneComparison_cornerHomology parabolicFaceArrow fullFlagLabels (flagParabolicResolution.π.f 0)
    flagParabolicResolution.complex_d_comp_π_f_zero canonicalFaceArrow (𝟙 _) (𝟙 _)
    canonicalFaceSquare (flagParabolicResolution.π.f 0)
    flagParabolicResolution.complex_d_comp_π_f_zero (Category.id_comp _)

/-- The complete forward face-to-canonical comparison preserves the exact augmented corner. -/
theorem fullFaceCanonical_corner :
    homologyMap (fullFaceConeParabolicEquiv.hom ≫ parabolicCanonicalEquiv.hom) 1 ≫ canonicalCorner =
      fullGeometricCorner := by
  rw [fullFaceConeParabolicEquiv_hom, parabolicCanonicalEquiv_hom,
    homologyMap_comp, Category.assoc, parabolicToCanonical_corner, fullFaceConeToParabolic_corner]

/-- The canonical model carries the same actual edge functional, through the genuine boundary equivalence. -/
theorem canonicalBoundary_corner :
    homologyMap canonicalBoundaryEquiv.hom 1 ≫ canonicalCorner =
      homologyMap fullFaceBoundaryEquiv.inv 1 ≫ fullGeometricCorner := by
  change homologyMap ((fullFaceBoundaryEquiv.inv ≫ fullFaceConeParabolicEquiv.hom) ≫
    parabolicCanonicalEquiv.hom) 1 ≫ canonicalCorner = _
  rw [Category.assoc, homologyMap_comp, Category.assoc, fullFaceCanonical_corner]

/-- On every actual canonical cone cycle the corner map is the complete literal B-augmentation. -/
theorem canonicalCorner_projection :
    canonicalFaceCone.homologyπ 1 ≫ canonicalCorner =
      canonicalFaceCone.iCycles 1 ≫ CofiberSequence.first canonicalFaceArrow 0 ≫
        flagParabolicResolution.π.f 0 :=
  coneCornerHomology_projection canonicalFaceArrow fullFlagLabels (flagParabolicResolution.π.f 0)
    flagParabolicResolution.complex_d_comp_π_f_zero

end TernaryPoly.OrdinaryBoundaryActualEvaluation
