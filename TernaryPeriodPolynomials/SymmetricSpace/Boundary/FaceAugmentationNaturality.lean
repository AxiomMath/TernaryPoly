module

public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.FaceAugmentationModels
public import TernaryPeriodPolynomials.Topology.Singular.ComponentAugmentationNaturality

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceBoundaryFaceAugmentation
open CategoryTheory Limits HomologicalComplex EquivariantSingularResolution FreeActionLinearization
open OrdinaryIncidence SymmetricSpaceBoundaryFaces SymmetricSpaceBoundaryMV
  IntegralGL3Congruence SingularBoundaryRestriction
open scoped MonoidAlgebra

attribute [local instance] lineLabelTopology planeLabelTopology flagLabelTopology
  lineLabelDiscrete planeLabelDiscrete flagLabelDiscrete

def flagLine : Flag → Line := fun F => F.val.1
def flagPlane : Flag → Plane := fun F => F.val.2

theorem flagLine_equivariant (g : principalSix) (F : Flag) : flagLine (g • F)=g • flagLine F := rfl
theorem flagPlane_equivariant (g : principalSix) (F : Flag) : flagPlane (g • F)=g • flagPlane F := rfl

/-- The actual flag-to-line permutation-module incidence map. -/
def lineIncidence : flagLabels ⟶ lineLabels :=
  SingularComponentAugmentation.permutationMap flagLine flagLine_equivariant

/-- The actual flag-to-plane permutation-module incidence map. -/
def planeIncidence : flagLabels ⟶ planeLabels :=
  SingularComponentAugmentation.permutationMap flagPlane flagPlane_equivariant

@[simp] theorem lineIncidence_single (F : Flag) (r : ℚ) :
    lineIncidence (MonoidAlgebra.single F r)=MonoidAlgebra.single F.val.1 r :=
  SingularComponentAugmentation.permutationMap_single _ _ _ _

@[simp] theorem planeIncidence_single (F : Flag) (r : ℚ) :
    planeIncidence (MonoidAlgebra.single F r)=MonoidAlgebra.single F.val.2 r :=
  SingularComponentAugmentation.permutationMap_single _ _ _ _

def lineFaceMap : TopCat.of CornerFaceSum ⟶ TopCat.of LineFaceSum := TopCat.ofHom cornerToLineSum
def planeFaceMap : TopCat.of CornerFaceSum ⟶ TopCat.of PlaneFaceSum := TopCat.ofHom cornerToPlaneSum

theorem lineFaceMap_equivariant (g : principalSix) (x : CornerFaceSum) :
    lineFaceMap (g • x)=g • lineFaceMap x := by
  apply lineFaceSumHomeomorph.injective
  rw [lineFaceSumHomeomorph_equivariant]
  change lineFaceSumHomeomorph (lineFaceSumHomeomorph.symm
    (cornerToLine (cornerFaceSumHomeomorph (g • x)))) =
      g • lineFaceSumHomeomorph (lineFaceSumHomeomorph.symm
        (cornerToLine (cornerFaceSumHomeomorph x)))
  rw [Homeomorph.apply_symm_apply,Homeomorph.apply_symm_apply,cornerFaceSumHomeomorph_equivariant]
  rfl

theorem planeFaceMap_equivariant (g : principalSix) (x : CornerFaceSum) :
    planeFaceMap (g • x)=g • planeFaceMap x := by
  apply planeFaceSumHomeomorph.injective
  rw [planeFaceSumHomeomorph_equivariant]
  change planeFaceSumHomeomorph (planeFaceSumHomeomorph.symm
    (cornerToPlane (cornerFaceSumHomeomorph (g • x)))) =
      g • planeFaceSumHomeomorph (planeFaceSumHomeomorph.symm
        (cornerToPlane (cornerFaceSumHomeomorph x)))
  rw [Homeomorph.apply_symm_apply,Homeomorph.apply_symm_apply,cornerFaceSumHomeomorph_equivariant]
  rfl

theorem lineFaceMap_label (x : CornerFaceSum) : (lineFaceMap x).1=flagLine x.1 := by
  rcases x with ⟨F,x⟩
  exact congrArg Sigma.fst (cornerToLineSum_apply F x)

theorem planeFaceMap_label (x : CornerFaceSum) : (planeFaceMap x).1=flagPlane x.1 := by
  rcases x with ⟨F,x⟩
  exact congrArg Sigma.fst (cornerToPlaneSum_apply F x)

def lineChainMap : flagChains ⟶ lineChains :=
  SingularCoverNaturality.chainMap lineFaceMap lineFaceMap_equivariant

def planeChainMap : flagChains ⟶ planeChains :=
  SingularCoverNaturality.chainMap planeFaceMap planeFaceMap_equivariant

theorem lineAugmentation_natural : lineChainMap.f 0 ≫ lineAugmentation=flagAugmentation ≫ lineIncidence :=
  SingularComponentAugmentation.augmentation_natural flagFamily lineFamily
    flagLabel_equivariant lineLabel_equivariant flagLine flagLine_equivariant
    lineFaceMap lineFaceMap_equivariant lineFaceMap_label

theorem planeAugmentation_natural : planeChainMap.f 0 ≫ planeAugmentation=flagAugmentation ≫ planeIncidence :=
  SingularComponentAugmentation.augmentation_natural flagFamily planeFamily
    flagLabel_equivariant planeLabel_equivariant flagPlane flagPlane_equivariant
    planeFaceMap planeFaceMap_equivariant planeFaceMap_label

theorem lineAugmentationChain_natural : lineChainMap ≫ lineAugmentationChain=
    flagAugmentationChain ≫ (ChainComplex.single₀ (Rep ℚ principalSix)).map lineIncidence :=
  SingularComponentAugmentation.augmentationChain_natural flagFamily lineFamily
    flagLabel_equivariant lineLabel_equivariant flagLine flagLine_equivariant
    lineFaceMap lineFaceMap_equivariant lineFaceMap_label

theorem planeAugmentationChain_natural : planeChainMap ≫ planeAugmentationChain=
    flagAugmentationChain ≫ (ChainComplex.single₀ (Rep ℚ principalSix)).map planeIncidence :=
  SingularComponentAugmentation.augmentationChain_natural flagFamily planeFamily
    flagLabel_equivariant planeLabel_equivariant flagPlane flagPlane_equivariant
    planeFaceMap planeFaceMap_equivariant planeFaceMap_label

/-- Literal corner inclusion induces precisely flag-to-line incidence on actual H0. -/
theorem lineH0_natural : homologyMap lineChainMap 0 ≫ lineH0Iso.hom=flagH0Iso.hom ≫ lineIncidence :=
  SingularComponentAugmentation.homologyZeroIso_natural flagFamily lineFamily
    flagLabel_equivariant lineLabel_equivariant flagLine flagLine_equivariant
    lineFaceMap lineFaceMap_equivariant lineFaceMap_label

/-- Literal corner inclusion induces precisely flag-to-plane incidence on actual H0. -/
theorem planeH0_natural : homologyMap planeChainMap 0 ≫ planeH0Iso.hom=flagH0Iso.hom ≫ planeIncidence :=
  SingularComponentAugmentation.homologyZeroIso_natural flagFamily planeFamily
    flagLabel_equivariant planeLabel_equivariant flagPlane flagPlane_equivariant
    planeFaceMap planeFaceMap_equivariant planeFaceMap_label

/-- The literal geometric incidence chain map is a morphism of the actual projective resolutions. -/
def lineResolutionMap : ProjectiveResolution.Hom flagResolution lineResolution lineIncidence where
  hom := lineChainMap
  hom_f_zero_comp_π_f_zero := by
    change lineChainMap.f 0 ≫ lineAugmentation=flagAugmentation ≫ lineIncidence
    exact lineAugmentation_natural

def planeResolutionMap : ProjectiveResolution.Hom flagResolution planeResolution planeIncidence where
  hom := planeChainMap
  hom_f_zero_comp_π_f_zero := by
    change planeChainMap.f 0 ≫ planeAugmentation=flagAugmentation ≫ planeIncidence
    exact planeAugmentation_natural

end TernaryPoly.SymmetricSpaceBoundaryFaceAugmentation
