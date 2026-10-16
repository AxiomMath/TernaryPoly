module

public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.FullStabilizers
public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.FullProjective

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceBoundaryFull
open CategoryTheory HomologicalComplex ModThreeGoodAction IntegralGL3Congruence OrdinaryIncidence
open SymmetricSpaceRationalGluing SymmetricSpaceBoundaryFaces SymmetricSpaceBoundaryMV
open SingularBoundaryRestriction EquivariantSingularResolution SymmetricSpaceBoundaryFullTransfer

/-- Full integral matrices preserve the entire union of line faces. -/
theorem fullLineSide_preserved (g : IntegralGL) {x : BoundaryCover} (hx : x ∈ lineSide) :
    g • x ∈ lineSide := by
  obtain ⟨L,hL⟩ := Set.mem_iUnion.mp hx
  apply Set.mem_iUnion.mpr
  refine ⟨g • L,?_⟩
  exact (lineFace_action_iff (integralRational g) L x.val).mpr hL

/-- Full integral matrices preserve the entire union of plane faces. -/
theorem fullPlaneSide_preserved (g : IntegralGL) {x : BoundaryCover} (hx : x ∈ planeSide) :
    g • x ∈ planeSide := by
  obtain ⟨P,hP⟩ := Set.mem_iUnion.mp hx
  apply Set.mem_iUnion.mpr
  refine ⟨g • P,?_⟩
  exact (planeFace_action_iff (integralRational g) P x.val).mpr hP

instance fullLineSideAction : MulAction IntegralGL lineSide where
  smul g x := ⟨g • x.val,fullLineSide_preserved g x.property⟩
  one_smul x := Subtype.ext (one_smul IntegralGL x.val)
  mul_smul g h x := Subtype.ext (mul_smul g h x.val)

instance fullPlaneSideAction : MulAction IntegralGL planeSide where
  smul g x := ⟨g • x.val,fullPlaneSide_preserved g x.property⟩
  one_smul x := Subtype.ext (one_smul IntegralGL x.val)
  mul_smul g h x := Subtype.ext (mul_smul g h x.val)

instance fullCornerAction : MulAction IntegralGL cornerLocus where
  smul g x := ⟨g • x.val,⟨fullLineSide_preserved g x.property.1,fullPlaneSide_preserved g x.property.2⟩⟩
  one_smul x := Subtype.ext (one_smul IntegralGL x.val)
  mul_smul g h x := Subtype.ext (mul_smul g h x.val)

instance fullLineSideContinuous : ContinuousConstSMul IntegralGL lineSide :=
  ⟨fun g => ((continuous_const_smul g).comp continuous_subtype_val).subtype_mk _⟩
instance fullPlaneSideContinuous : ContinuousConstSMul IntegralGL planeSide :=
  ⟨fun g => ((continuous_const_smul g).comp continuous_subtype_val).subtype_mk _⟩
instance fullCornerContinuous : ContinuousConstSMul IntegralGL cornerLocus :=
  ⟨fun g => ((continuous_const_smul g).comp continuous_subtype_val).subtype_mk _⟩

instance fullLineSumAction : MulAction IntegralGL LineFaceSum := lineFaceSumHomeomorph.toEquiv.mulAction _
instance fullPlaneSumAction : MulAction IntegralGL PlaneFaceSum := planeFaceSumHomeomorph.toEquiv.mulAction _
instance fullFlagSumAction : MulAction IntegralGL CornerFaceSum := cornerFaceSumHomeomorph.toEquiv.mulAction _

instance fullLineSumContinuous : ContinuousConstSMul IntegralGL LineFaceSum :=
  ⟨fun g => lineFaceSumHomeomorph.symm.continuous.comp
    ((continuous_const_smul g).comp lineFaceSumHomeomorph.continuous)⟩
instance fullPlaneSumContinuous : ContinuousConstSMul IntegralGL PlaneFaceSum :=
  ⟨fun g => planeFaceSumHomeomorph.symm.continuous.comp
    ((continuous_const_smul g).comp planeFaceSumHomeomorph.continuous)⟩
instance fullFlagSumContinuous : ContinuousConstSMul IntegralGL CornerFaceSum :=
  ⟨fun g => cornerFaceSumHomeomorph.symm.continuous.comp
    ((continuous_const_smul g).comp cornerFaceSumHomeomorph.continuous)⟩

theorem fullLineSum_value (g : IntegralGL) (x : LineFaceSum) : (g • x).2.val = g • x.2.val :=
  congrArg (fun y : lineSide => y.val.val) (lineFaceSumHomeomorph.apply_symm_apply _)
theorem fullPlaneSum_value (g : IntegralGL) (x : PlaneFaceSum) : (g • x).2.val = g • x.2.val :=
  congrArg (fun y : planeSide => y.val.val) (planeFaceSumHomeomorph.apply_symm_apply _)
theorem fullFlagSum_value (g : IntegralGL) (x : CornerFaceSum) : (g • x).2.val = g • x.2.val :=
  congrArg (fun y : cornerLocus => y.val.val) (cornerFaceSumHomeomorph.apply_symm_apply _)

theorem fullLineSum_label (g : IntegralGL) (x : LineFaceSum) : (g • x).1 = g • x.1 := by
  have h := (g • x).2.property
  rw [fullLineSum_value] at h
  apply lineFace_unique h
  exact (lineFace_action_iff (integralRational g) x.1 x.2.val).mpr x.2.property

theorem fullPlaneSum_label (g : IntegralGL) (x : PlaneFaceSum) : (g • x).1 = g • x.1 := by
  have h := (g • x).2.property
  rw [fullPlaneSum_value] at h
  apply planeFace_unique h
  exact (planeFace_action_iff (integralRational g) x.1 x.2.val).mpr x.2.property

theorem fullFlagSum_label (g : IntegralGL) (x : CornerFaceSum) : (g • x).1 = g • x.1 := by
  have h := (g • x).2.property
  rw [fullFlagSum_value] at h
  apply flagFace_unique h
  exact ⟨(lineFace_action_iff (integralRational g) _ _).mpr x.2.property.1,
    (planeFace_action_iff (integralRational g) _ _).mpr x.2.property.2⟩

theorem fullLineSum_restrict (g : principalSix) (x : LineFaceSum) : (g.val : IntegralGL) • x = g • x := rfl
theorem fullPlaneSum_restrict (g : principalSix) (x : PlaneFaceSum) : (g.val : IntegralGL) • x = g • x := rfl
theorem fullFlagSum_restrict (g : principalSix) (x : CornerFaceSum) : (g.val : IntegralGL) • x = g • x := rfl

end TernaryPoly.SymmetricSpaceBoundaryFull
