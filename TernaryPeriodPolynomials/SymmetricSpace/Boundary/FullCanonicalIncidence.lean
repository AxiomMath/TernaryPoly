module

public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.FullInducedBarShapiro
public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.FullParabolicTotal

@[expose] public section

noncomputable section
namespace TernaryPoly.SymmetricSpaceBoundaryFull
open CategoryTheory HomologicalComplex Representation ModThreeGoodAction
open SymmetricSpaceBoundaryFaceAugmentation
open OrdinaryParabolicGroups SymmetricSpaceBoundaryMV OrdinaryIncidence SymmetricSpaceBoundaryFaces

theorem fullB_le_Q : B ≤ Q := inf_le_right
theorem fullB_le_P : B ≤ P := inf_le_left

/-- Canonical full flag-to-line map, induced by the literal subgroup inclusion B ≤ Q. -/
def canonicalLineArrow : inducedBarComplex B ⟶ inducedBarComplex Q :=
  inducedBarMap B Q fullB_le_Q

/-- Canonical full flag-to-plane map, induced by the literal subgroup inclusion B ≤ P. -/
def canonicalPlaneArrow : inducedBarComplex B ⟶ inducedBarComplex P :=
  inducedBarMap B P fullB_le_P

/-- The canonical induced B→Q map covers the actual flag-to-line label incidence. -/
def canonicalLineResolutionMap :
    ProjectiveResolution.Hom flagParabolicResolution lineParabolicResolution fullLineIncidence where
  hom := canonicalLineArrow
  hom_f_zero_comp_π_f_zero := by
    apply Rep.hom_ext
    apply IntertwiningMap.ext
    apply IndV.hom_ext
    intro g
    apply LinearMap.ext
    intro b
    change ((lineParabolicResolution).π.f 0).hom
      ((inducedBarDegree B Q fullB_le_Q 0).hom (IndV.mk _ _ g b)) =
      fullLineIncidence.hom ((flagParabolicResolution.π.f 0).hom (IndV.mk _ _ g b))
    rw [inducedBarDegree_mk]
    have hl := fullParabolicAt_augmentation standardLine fullLine_transitive Q standardLine_stabilizer g
      ((subgroupBarDegree B Q fullB_le_Q 0).hom b)
    have hb := fullParabolicAt_augmentation standardFlag fullFlag_transitive B standardFlag_stabilizer g b
    refine hl.trans ?_
    refine Eq.trans ?_ (congrArg (fun x => fullLineIncidence.hom x) hb).symm
    change MonoidAlgebra.single (g⁻¹ • standardLine) _ =
      fullLineIncidence.hom (MonoidAlgebra.single (g⁻¹ • standardFlag) _)
    have haug := subgroupBarDegree_augmentation B Q fullB_le_Q b
    have hperm := SingularComponentAugmentation.permutationMap_single flagLine
      (fun (_ : IntegralGL) _ => rfl) (g⁻¹ • standardFlag)
      ((SingularCoverRestriction.barAugmentation (G := B)).hom b)
    exact (congrArg (fun z : ℚ => MonoidAlgebra.single (g⁻¹ • standardLine) z) haug).trans hperm.symm

/-- The canonical induced B→P map covers the actual flag-to-plane label incidence. -/
def canonicalPlaneResolutionMap :
    ProjectiveResolution.Hom flagParabolicResolution planeParabolicResolution fullPlaneIncidence where
  hom := canonicalPlaneArrow
  hom_f_zero_comp_π_f_zero := by
    apply Rep.hom_ext
    apply IntertwiningMap.ext
    apply IndV.hom_ext
    intro g
    apply LinearMap.ext
    intro b
    change ((planeParabolicResolution).π.f 0).hom
      ((inducedBarDegree B P fullB_le_P 0).hom (IndV.mk _ _ g b)) =
      fullPlaneIncidence.hom ((flagParabolicResolution.π.f 0).hom (IndV.mk _ _ g b))
    rw [inducedBarDegree_mk]
    have hl := fullParabolicAt_augmentation standardPlane fullPlane_transitive P standardPlane_stabilizer g
      ((subgroupBarDegree B P fullB_le_P 0).hom b)
    have hb := fullParabolicAt_augmentation standardFlag fullFlag_transitive B standardFlag_stabilizer g b
    refine hl.trans ?_
    refine Eq.trans ?_ (congrArg (fun x => fullPlaneIncidence.hom x) hb).symm
    change MonoidAlgebra.single (g⁻¹ • standardPlane) _ =
      fullPlaneIncidence.hom (MonoidAlgebra.single (g⁻¹ • standardFlag) _)
    have haug := subgroupBarDegree_augmentation B P fullB_le_P b
    have hperm := SingularComponentAugmentation.permutationMap_single flagPlane
      (fun (_ : IntegralGL) _ => rfl) (g⁻¹ • standardFlag)
      ((SingularCoverRestriction.barAugmentation (G := B)).hom b)
    exact (congrArg (fun z : ℚ => MonoidAlgebra.single (g⁻¹ • standardPlane) z) haug).trans hperm.symm

/-- The chosen projective lift is canonically homotopic to genuine subgroup restriction. -/
def canonicalLineHomotopy : Homotopy parabolicLineArrow canonicalLineArrow :=
  ProjectiveResolution.liftHomotopy fullLineIncidence _ _
    (ProjectiveResolution.lift_commutes _ _ _) canonicalLineResolutionMap.hom_comp_π

def canonicalPlaneHomotopy : Homotopy parabolicPlaneArrow canonicalPlaneArrow :=
  ProjectiveResolution.liftHomotopy fullPlaneIncidence _ _
    (ProjectiveResolution.lift_commutes _ _ _) canonicalPlaneResolutionMap.hom_comp_π

end TernaryPoly.SymmetricSpaceBoundaryFull
