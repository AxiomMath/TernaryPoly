module

public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.MVFaceSums

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceBoundaryMV
open Topology OrdinaryIncidence SymmetricSpaceRationalGluing SymmetricSpaceBoundaryFaces
  SymmetricSpaceBoundaryFaceTopology SingularBoundaryRestriction IntegralGL3Congruence
open scoped unitInterval

instance lineFaceSumContinuous : ContinuousConstSMul principalSix LineFaceSum :=
  ⟨fun g => lineFaceSumHomeomorph.symm.continuous.comp
    ((continuous_const_smul g).comp lineFaceSumHomeomorph.continuous)⟩
instance planeFaceSumContinuous : ContinuousConstSMul principalSix PlaneFaceSum :=
  ⟨fun g => planeFaceSumHomeomorph.symm.continuous.comp
    ((continuous_const_smul g).comp planeFaceSumHomeomorph.continuous)⟩
instance cornerFaceSumContinuous : ContinuousConstSMul principalSix CornerFaceSum :=
  ⟨fun g => cornerFaceSumHomeomorph.symm.continuous.comp
    ((continuous_const_smul g).comp cornerFaceSumHomeomorph.continuous)⟩

theorem lineFaceSum_smul_label (g : principalSix) (x : LineFaceSum) :
    (g • x).1=OrdinaryFullAction.lineAction (OrdinaryFullAction.integral g.val) x.1 := by
  have h := (g • x).2.property
  rw [lineFaceSum_smul_val] at h
  apply lineFace_unique h
  rw [←principalSix_lineFace_image]
  exact ⟨x.2.val,x.2.property,rfl⟩

theorem planeFaceSum_smul_label (g : principalSix) (x : PlaneFaceSum) :
    (g • x).1=OrdinaryFullAction.planeAction (OrdinaryFullAction.integral g.val) x.1 := by
  have h := (g • x).2.property
  rw [planeFaceSum_smul_val] at h
  apply planeFace_unique h
  rw [←principalSix_planeFace_image]
  exact ⟨x.2.val,x.2.property,rfl⟩

theorem cornerFaceSum_smul_label (g : principalSix) (x : CornerFaceSum) :
    (g • x).1=flagAction g x.1 := by
  have h := (g • x).2.property
  rw [cornerFaceSum_smul_val] at h
  apply flagFace_unique h
  rw [←flagFace_image]
  exact ⟨x.2.val,x.2.property,rfl⟩

def cornerToLineSum : C(CornerFaceSum,LineFaceSum) :=
  lineFaceSumHomeomorph.symm.toHomotopyEquiv.toFun.comp
    (cornerToLine.comp cornerFaceSumHomeomorph.toHomotopyEquiv.toFun)
def cornerToPlaneSum : C(CornerFaceSum,PlaneFaceSum) :=
  planeFaceSumHomeomorph.symm.toHomotopyEquiv.toFun.comp
    (cornerToPlane.comp cornerFaceSumHomeomorph.toHomotopyEquiv.toFun)

/-- The sum-level corner map is the literal full-flag-to-line-face inclusion. -/
theorem cornerToLineSum_apply (F : Flag) (x : flagFace F) :
    cornerToLineSum ⟨F,x⟩=⟨F.val.1,⟨x.val,x.property.1⟩⟩ := by
  apply lineFaceSumHomeomorph.injective
  change lineFaceSumHomeomorph (lineFaceSumHomeomorph.symm _)=_
  rw [Homeomorph.apply_symm_apply]
  rfl

theorem cornerToPlaneSum_apply (F : Flag) (x : flagFace F) :
    cornerToPlaneSum ⟨F,x⟩=⟨F.val.2,⟨x.val,x.property.2⟩⟩ := by
  apply planeFaceSumHomeomorph.injective
  change planeFaceSumHomeomorph (planeFaceSumHomeomorph.symm _)=_
  rw [Homeomorph.apply_symm_apply]
  rfl

def lineSumRetraction : C(UpstairsLine,LineFaceSum) :=
  lineFaceSumHomeomorph.symm.toHomotopyEquiv.toFun.comp lineRetraction
def planeSumRetraction : C(UpstairsPlane,PlaneFaceSum) :=
  planeFaceSumHomeomorph.symm.toHomotopyEquiv.toFun.comp planeRetraction
def cornerSumRetraction : C(UpstairsOverlap,CornerFaceSum) :=
  cornerFaceSumHomeomorph.symm.toHomotopyEquiv.toFun.comp cornerRetraction

theorem lineSumRetraction_equivariant (g : principalSix) (x : UpstairsLine) :
    lineSumRetraction (g • x)=g • lineSumRetraction x := by
  apply lineFaceSumHomeomorph.injective
  rw [lineFaceSumHomeomorph_equivariant]
  change lineFaceSumHomeomorph (lineFaceSumHomeomorph.symm (lineRetraction (g • x)))=
    g • lineFaceSumHomeomorph (lineFaceSumHomeomorph.symm (lineRetraction x))
  rw [Homeomorph.apply_symm_apply,Homeomorph.apply_symm_apply,lineRetraction_equivariant]

theorem planeSumRetraction_equivariant (g : principalSix) (x : UpstairsPlane) :
    planeSumRetraction (g • x)=g • planeSumRetraction x := by
  apply planeFaceSumHomeomorph.injective
  rw [planeFaceSumHomeomorph_equivariant]
  change planeFaceSumHomeomorph (planeFaceSumHomeomorph.symm (planeRetraction (g • x)))=
    g • planeFaceSumHomeomorph (planeFaceSumHomeomorph.symm (planeRetraction x))
  rw [Homeomorph.apply_symm_apply,Homeomorph.apply_symm_apply,planeRetraction_equivariant]

theorem cornerSumRetraction_equivariant (g : principalSix) (x : UpstairsOverlap) :
    cornerSumRetraction (g • x)=g • cornerSumRetraction x := by
  apply cornerFaceSumHomeomorph.injective
  rw [cornerFaceSumHomeomorph_equivariant]
  change cornerFaceSumHomeomorph (cornerFaceSumHomeomorph.symm (cornerRetraction (g • x)))=
    g • cornerFaceSumHomeomorph (cornerFaceSumHomeomorph.symm (cornerRetraction x))
  rw [Homeomorph.apply_symm_apply,Homeomorph.apply_symm_apply,cornerRetraction_equivariant]

def lineSumCompatibility : ContinuousMap.Homotopy
    (lineSumRetraction.comp overlapToLine) (cornerToLineSum.comp cornerSumRetraction) where
  toFun z := lineFaceSumHomeomorph.symm (lineCompatibility z)
  continuous_toFun := lineFaceSumHomeomorph.symm.continuous.comp lineCompatibility.continuous
  map_zero_left x := congrArg lineFaceSumHomeomorph.symm (lineCompatibility.map_zero_left x)
  map_one_left x := by
    change lineFaceSumHomeomorph.symm (lineCompatibility (1,x))=
      lineFaceSumHomeomorph.symm (cornerToLine (cornerFaceSumHomeomorph
        (cornerFaceSumHomeomorph.symm (cornerRetraction x))))
    rw [Homeomorph.apply_symm_apply]
    exact congrArg lineFaceSumHomeomorph.symm (lineCompatibility.map_one_left x)

def planeSumCompatibility : ContinuousMap.Homotopy
    (planeSumRetraction.comp overlapToPlane) (cornerToPlaneSum.comp cornerSumRetraction) where
  toFun z := planeFaceSumHomeomorph.symm (planeCompatibility z)
  continuous_toFun := planeFaceSumHomeomorph.symm.continuous.comp planeCompatibility.continuous
  map_zero_left x := congrArg planeFaceSumHomeomorph.symm (planeCompatibility.map_zero_left x)
  map_one_left x := by
    change planeFaceSumHomeomorph.symm (planeCompatibility (1,x))=
      planeFaceSumHomeomorph.symm (cornerToPlane (cornerFaceSumHomeomorph
        (cornerFaceSumHomeomorph.symm (cornerRetraction x))))
    rw [Homeomorph.apply_symm_apply]
    exact congrArg planeFaceSumHomeomorph.symm (planeCompatibility.map_one_left x)

theorem lineSumCompatibility_equivariant (g : principalSix) (t : I) (x : UpstairsOverlap) :
    lineSumCompatibility (t,g • x)=g • lineSumCompatibility (t,x) := by
  apply lineFaceSumHomeomorph.injective
  rw [lineFaceSumHomeomorph_equivariant]
  change lineFaceSumHomeomorph (lineFaceSumHomeomorph.symm (lineCompatibility (t,g • x)))=
    g • lineFaceSumHomeomorph (lineFaceSumHomeomorph.symm (lineCompatibility (t,x)))
  rw [Homeomorph.apply_symm_apply,Homeomorph.apply_symm_apply,lineCompatibility_equivariant]

theorem planeSumCompatibility_equivariant (g : principalSix) (t : I) (x : UpstairsOverlap) :
    planeSumCompatibility (t,g • x)=g • planeSumCompatibility (t,x) := by
  apply planeFaceSumHomeomorph.injective
  rw [planeFaceSumHomeomorph_equivariant]
  change planeFaceSumHomeomorph (planeFaceSumHomeomorph.symm (planeCompatibility (t,g • x)))=
    g • planeFaceSumHomeomorph (planeFaceSumHomeomorph.symm (planeCompatibility (t,x)))
  rw [Homeomorph.apply_symm_apply,Homeomorph.apply_symm_apply,planeCompatibility_equivariant]

theorem lineFaceSumEquiv_equivariant (g : principalSix) (x : LineFaceSum) :
    lineFaceSumEquiv (g • x)=g • lineFaceSumEquiv x :=
  Subtype.ext (congrArg (fun y : lineSide => y.val) (lineFaceSumHomeomorph_equivariant g x))

@[simp] theorem lineSumRetraction_inclusion (x : LineFaceSum) :
    lineSumRetraction (lineFaceSumEquiv x)=x := by
  apply lineFaceSumHomeomorph.injective
  change lineFaceSumHomeomorph (lineFaceSumHomeomorph.symm
    (lineRetraction (lineFaceSumEquiv x)))=lineFaceSumHomeomorph x
  rw [Homeomorph.apply_symm_apply]
  apply Subtype.ext
  exact lineRetraction_fixed _ (lineFaceSumHomeomorph x).property

/-- The explicit equivariant deformation inverse to the entire-face inclusion. -/
def lineSumDeformation : ContinuousMap.Homotopy (ContinuousMap.id UpstairsLine)
    (lineFaceSumEquiv.toFun.comp lineSumRetraction) where
  toFun := lineBaseRetraction.selfLift
  continuous_toFun := lineBaseRetraction.selfLift.continuous
  map_zero_left x := Subtype.ext (lineBaseRetraction.lift_zero x)
  map_one_left x := by
    apply Subtype.ext
    change lineBaseRetraction.lift (1,x)=
      (lineFaceSumHomeomorph (lineFaceSumHomeomorph.symm (lineRetraction x))).val
    rw [Homeomorph.apply_symm_apply]
    rfl

theorem lineSumDeformation_equivariant (g : principalSix) (t : I) (x : UpstairsLine) :
    lineSumDeformation (t,g • x)=g • lineSumDeformation (t,x) :=
  lineBaseRetraction.selfLift_equivariant g t x

theorem planeFaceSumEquiv_equivariant (g : principalSix) (x : PlaneFaceSum) :
    planeFaceSumEquiv (g • x)=g • planeFaceSumEquiv x :=
  Subtype.ext (congrArg (fun y : planeSide => y.val) (planeFaceSumHomeomorph_equivariant g x))

@[simp] theorem planeSumRetraction_inclusion (x : PlaneFaceSum) :
    planeSumRetraction (planeFaceSumEquiv x)=x := by
  apply planeFaceSumHomeomorph.injective
  change planeFaceSumHomeomorph (planeFaceSumHomeomorph.symm
    (planeRetraction (planeFaceSumEquiv x)))=planeFaceSumHomeomorph x
  rw [Homeomorph.apply_symm_apply]
  apply Subtype.ext
  exact planeRetraction_fixed _ (planeFaceSumHomeomorph x).property

/-- The explicit equivariant deformation inverse to the entire-face inclusion. -/
def planeSumDeformation : ContinuousMap.Homotopy (ContinuousMap.id UpstairsPlane)
    (planeFaceSumEquiv.toFun.comp planeSumRetraction) where
  toFun := planeBaseRetraction.selfLift
  continuous_toFun := planeBaseRetraction.selfLift.continuous
  map_zero_left x := Subtype.ext (planeBaseRetraction.lift_zero x)
  map_one_left x := by
    apply Subtype.ext
    change planeBaseRetraction.lift (1,x)=
      (planeFaceSumHomeomorph (planeFaceSumHomeomorph.symm (planeRetraction x))).val
    rw [Homeomorph.apply_symm_apply]
    rfl

theorem planeSumDeformation_equivariant (g : principalSix) (t : I) (x : UpstairsPlane) :
    planeSumDeformation (t,g • x)=g • planeSumDeformation (t,x) :=
  planeBaseRetraction.selfLift_equivariant g t x

theorem cornerFaceSumEquiv_equivariant (g : principalSix) (x : CornerFaceSum) :
    cornerFaceSumEquiv (g • x)=g • cornerFaceSumEquiv x :=
  Subtype.ext (congrArg (fun y : cornerLocus => y.val) (cornerFaceSumHomeomorph_equivariant g x))

@[simp] theorem cornerSumRetraction_inclusion (x : CornerFaceSum) :
    cornerSumRetraction (cornerFaceSumEquiv x)=x := by
  apply cornerFaceSumHomeomorph.injective
  change cornerFaceSumHomeomorph (cornerFaceSumHomeomorph.symm
    (cornerRetraction (cornerFaceSumEquiv x)))=cornerFaceSumHomeomorph x
  rw [Homeomorph.apply_symm_apply]
  apply Subtype.ext
  exact cornerRetraction_fixed _ (cornerFaceSumHomeomorph x).property

/-- The explicit equivariant deformation inverse to the entire-face inclusion. -/
def cornerSumDeformation : ContinuousMap.Homotopy (ContinuousMap.id UpstairsOverlap)
    (cornerFaceSumEquiv.toFun.comp cornerSumRetraction) where
  toFun := cornerBaseRetraction.selfLift
  continuous_toFun := cornerBaseRetraction.selfLift.continuous
  map_zero_left x := Subtype.ext (cornerBaseRetraction.lift_zero x)
  map_one_left x := by
    apply Subtype.ext
    change cornerBaseRetraction.lift (1,x)=
      (cornerFaceSumHomeomorph (cornerFaceSumHomeomorph.symm (cornerRetraction x))).val
    rw [Homeomorph.apply_symm_apply]
    rfl

theorem cornerSumDeformation_equivariant (g : principalSix) (t : I) (x : UpstairsOverlap) :
    cornerSumDeformation (t,g • x)=g • cornerSumDeformation (t,x) :=
  cornerBaseRetraction.selfLift_equivariant g t x

/-- Consumer summary: a genuine invariant open cover of the literal boundary, with entire-face
and entire-corner homotopy models. Explicit equivariant retractions and compatibility homotopies
are the declarations above; this theorem makes no claim about cohomology or cone comparison. -/
theorem actual_open_mayer_vietoris_cover :
    IsOpen UpstairsLine ∧ IsOpen UpstairsPlane ∧
    UpstairsLine ∪ UpstairsPlane=Set.univ ∧ UpstairsLine ∩ UpstairsPlane=UpstairsOverlap ∧
    (∀ (g : principalSix) (x : BoundaryCover),g • x∈UpstairsLine ↔ x∈UpstairsLine) ∧
    (∀ (g : principalSix) (x : BoundaryCover),g • x∈UpstairsPlane ↔ x∈UpstairsPlane) ∧
    Nonempty (ContinuousMap.HomotopyEquiv LineFaceSum UpstairsLine) ∧
    Nonempty (ContinuousMap.HomotopyEquiv PlaneFaceSum UpstairsPlane) ∧
    Nonempty (ContinuousMap.HomotopyEquiv CornerFaceSum UpstairsOverlap) :=
  ⟨upstairsLine_open,upstairsPlane_open,upstairs_cover,upstairs_inter,
    upstairs_invariant _,upstairs_invariant _,⟨lineFaceSumEquiv⟩,⟨planeFaceSumEquiv⟩,⟨cornerFaceSumEquiv⟩⟩

end TernaryPoly.SymmetricSpaceBoundaryMV
