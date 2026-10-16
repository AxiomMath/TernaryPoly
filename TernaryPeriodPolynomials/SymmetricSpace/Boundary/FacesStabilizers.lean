module

public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.FacesAction
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Parabolic.GroupsBasic

@[expose] public section

noncomputable section
namespace TernaryPoly.SymmetricSpaceBoundaryFaces
open OrdinaryIncidence SymmetricSpaceRationalAction SymmetricSpaceRationalGluing
open SymmetricSpaceBorelCorner SymmetricSpaceLineBordification
open scoped Pointwise

/-- The setwise stabilizer of the actual standard line-face is the full rational line parabolic. -/
theorem standard_lineFace_stabilizer (a : RationalGL) :
    leftAction a '' lineFace standardLine=lineFace standardLine ↔ realRational a∈lineStabilizer := by
  rw [lineFace_image,lineFace_injective.eq_iff]
  change lineLabel a=standardLine ↔ _
  rw [←lineLabel_one,lineLabel_eq_iff]
  simp [changeMatrix]

/-- The setwise stabilizer of the actual standard plane-face is the full rational plane parabolic. -/
theorem standard_planeFace_stabilizer (a : RationalGL) :
    leftAction a '' planeFace standardPlane=planeFace standardPlane ↔ realRational a∈planeStabilizer := by
  rw [planeFace_image,planeFace_injective.eq_iff]
  change planeLabel a=standardPlane ↔ _
  rw [←planeLabel_one,planeLabel_eq_iff]
  simp [changeMatrix]

/-- The literal integral line-face fixer is exactly the existing full integral parabolic Q. -/
theorem integral_lineFace_stabilizer (a : ModThreeGoodAction.IntegralGL) :
    integralAction a '' lineFace standardLine=lineFace standardLine ↔ a∈OrdinaryParabolicGroups.Q := by
  change leftAction (integralRational a) '' lineFace standardLine=lineFace standardLine ↔ _
  rw [standard_lineFace_stabilizer,mem_lineStabilizer_iff,OrdinaryParabolicGroups.mem_Q]
  change (((a.val 1 0 : ℚ) : ℝ)=0 ∧ ((a.val 2 0 : ℚ) : ℝ)=0) ↔ _
  norm_cast

/-- The literal integral plane-face fixer is exactly the existing full integral parabolic P. -/
theorem integral_planeFace_stabilizer (a : ModThreeGoodAction.IntegralGL) :
    integralAction a '' planeFace standardPlane=planeFace standardPlane ↔ a∈OrdinaryParabolicGroups.P := by
  change leftAction (integralRational a) '' planeFace standardPlane=planeFace standardPlane ↔ _
  rw [standard_planeFace_stabilizer,mem_planeStabilizer_iff,OrdinaryParabolicGroups.mem_P]
  change (((a.val 2 0 : ℚ) : ℝ)=0 ∧ ((a.val 2 1 : ℚ) : ℝ)=0) ↔ _
  norm_cast

/-- The actual integral subgroup acting on the standard line face is precisely Q. -/
theorem integral_line_setStabilizer :
    MulAction.stabilizer ModThreeGoodAction.IntegralGL (lineFace standardLine)=OrdinaryParabolicGroups.Q := by
  ext a
  exact integral_lineFace_stabilizer a

theorem integral_plane_setStabilizer :
    MulAction.stabilizer ModThreeGoodAction.IntegralGL (planeFace standardPlane)=OrdinaryParabolicGroups.P := by
  ext a
  exact integral_planeFace_stabilizer a

/-- This identifies the face stabilizer for K, principal six, or any other actual integral subgroup. -/
theorem subgroup_line_setStabilizer (H : Subgroup ModThreeGoodAction.IntegralGL) :
    MulAction.stabilizer H (lineFace standardLine)=OrdinaryParabolicGroups.Q.comap H.subtype := by
  ext a
  exact integral_lineFace_stabilizer a.val

theorem subgroup_plane_setStabilizer (H : Subgroup ModThreeGoodAction.IntegralGL) :
    MulAction.stabilizer H (planeFace standardPlane)=OrdinaryParabolicGroups.P.comap H.subtype := by
  ext a
  exact integral_planeFace_stabilizer a.val

end TernaryPoly.SymmetricSpaceBoundaryFaces
