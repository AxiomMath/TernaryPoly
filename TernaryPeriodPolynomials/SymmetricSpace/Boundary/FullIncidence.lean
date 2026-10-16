module

public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.FullResolutions

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceBoundaryFull
open CategoryTheory Limits HomologicalComplex ModThreeGoodAction IntegralGL3Congruence
open SymmetricSpaceBoundaryMV EquivariantSingularResolution SingularCoverNaturality
open SymmetricSpaceBoundaryFaceAugmentation SymmetricSpaceBoundaryFullTransfer

attribute [local instance] fullLineLabelTopology fullPlaneLabelTopology fullFlagLabelTopology
  fullLineLabelDiscrete fullPlaneLabelDiscrete fullFlagLabelDiscrete

/-- Full arithmetic equivariance of the literal corner-to-line inclusion. -/
theorem fullLineFaceMap_equivariant (g : IntegralGL) (x : CornerFaceSum) :
    lineFaceMap (g • x) = g • lineFaceMap x := by
  apply lineFaceSumHomeomorph.injective
  change lineFaceSumHomeomorph (lineFaceSumHomeomorph.symm
    (cornerToLine (cornerFaceSumHomeomorph (g • x)))) =
      lineFaceSumHomeomorph (lineFaceSumHomeomorph.symm _)
  rw [Homeomorph.apply_symm_apply,Homeomorph.apply_symm_apply]
  rw [show cornerFaceSumHomeomorph (g • x) = g • cornerFaceSumHomeomorph x from
    cornerFaceSumHomeomorph.apply_symm_apply _]
  change cornerToLine (g • cornerFaceSumHomeomorph x) =
    g • lineFaceSumHomeomorph (lineFaceSumHomeomorph.symm (cornerToLine (cornerFaceSumHomeomorph x)))
  rw [Homeomorph.apply_symm_apply]
  rfl

theorem fullPlaneFaceMap_equivariant (g : IntegralGL) (x : CornerFaceSum) :
    planeFaceMap (g • x) = g • planeFaceMap x := by
  apply planeFaceSumHomeomorph.injective
  change planeFaceSumHomeomorph (planeFaceSumHomeomorph.symm
    (cornerToPlane (cornerFaceSumHomeomorph (g • x)))) =
      planeFaceSumHomeomorph (planeFaceSumHomeomorph.symm _)
  rw [Homeomorph.apply_symm_apply,Homeomorph.apply_symm_apply]
  rw [show cornerFaceSumHomeomorph (g • x) = g • cornerFaceSumHomeomorph x from
    cornerFaceSumHomeomorph.apply_symm_apply _]
  change cornerToPlane (g • cornerFaceSumHomeomorph x) =
    g • planeFaceSumHomeomorph (planeFaceSumHomeomorph.symm (cornerToPlane (cornerFaceSumHomeomorph x)))
  rw [Homeomorph.apply_symm_apply]
  rfl

def fullLineChainMap : fullFlagChains ⟶ fullLineChains := chainMap lineFaceMap fullLineFaceMap_equivariant
def fullPlaneChainMap : fullFlagChains ⟶ fullPlaneChains := chainMap planeFaceMap fullPlaneFaceMap_equivariant

def fullLineIncidence : fullFlagLabels ⟶ fullLineLabels :=
  SingularComponentAugmentation.permutationMap flagLine (fun (_ : IntegralGL) _ => rfl)
def fullPlaneIncidence : fullFlagLabels ⟶ fullPlaneLabels :=
  SingularComponentAugmentation.permutationMap flagPlane (fun (_ : IntegralGL) _ => rfl)

/-- The resolution morphisms lift the actual integral label incidence. -/
def fullLineResolutionMap : ProjectiveResolution.Hom fullFlagResolution fullLineResolution fullLineIncidence where
  hom := fullLineChainMap
  hom_f_zero_comp_π_f_zero := SingularComponentAugmentation.augmentation_natural flagFamily lineFamily
    fullFlagSum_label fullLineSum_label flagLine (fun (_ : IntegralGL) _ => rfl)
    lineFaceMap fullLineFaceMap_equivariant lineFaceMap_label

def fullPlaneResolutionMap : ProjectiveResolution.Hom fullFlagResolution fullPlaneResolution fullPlaneIncidence where
  hom := fullPlaneChainMap
  hom_f_zero_comp_π_f_zero := SingularComponentAugmentation.augmentation_natural flagFamily planeFamily
    fullFlagSum_label fullPlaneSum_label flagPlane (fun (_ : IntegralGL) _ => rfl)
    planeFaceMap fullPlaneFaceMap_equivariant planeFaceMap_label

/-- The geometric total keeps line-minus-plane, with no ordinary edge renormalization. -/
def fullFaceArrow : fullFlagChains ⟶ fullLineChains ⊞ fullPlaneChains :=
  biprod.lift fullLineChainMap (-fullPlaneChainMap)

abbrev fullFaceCone := homotopyCofiber fullFaceArrow

/-- Restricting the full face arrow preserves both literal singular incidence maps. -/
theorem fullLineChainMap_restrict :
    ((Rep.resFunctor principalSix.subtype).mapHomologicalComplex (ComplexShape.down ℕ)).map fullLineChainMap =
      lineChainMap := rfl

theorem fullPlaneChainMap_restrict :
    ((Rep.resFunctor principalSix.subtype).mapHomologicalComplex (ComplexShape.down ℕ)).map fullPlaneChainMap =
      planeChainMap := rfl

end TernaryPoly.SymmetricSpaceBoundaryFull
