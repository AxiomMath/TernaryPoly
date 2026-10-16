module

public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.MVLift

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceBoundaryMV
open Topology SingularBoundaryRestriction IntegralGL3Congruence
open scoped unitInterval

abbrev UpstairsLine := boundaryProjection ⁻¹' lineNeighborhood
abbrev UpstairsPlane := boundaryProjection ⁻¹' planeNeighborhood
abbrev UpstairsOverlap := boundaryProjection ⁻¹' collarNeighborhood

theorem upstairsLine_open : IsOpen UpstairsLine := lineNeighborhood_open.preimage boundaryCovering.continuous
theorem upstairsPlane_open : IsOpen UpstairsPlane := planeNeighborhood_open.preimage boundaryCovering.continuous

theorem upstairs_cover : UpstairsLine ∪ UpstairsPlane=Set.univ := by
  rw [←Set.preimage_union,neighborhoods_cover,Set.preimage_univ]

theorem upstairs_inter : UpstairsLine ∩ UpstairsPlane=UpstairsOverlap := by
  rw [←Set.preimage_inter,neighborhoods_inter]

theorem upstairs_invariant (S : Set BoundaryBase) (g : principalSix) (x : BoundaryCover) :
    g • x∈boundaryProjection ⁻¹' S ↔ x∈boundaryProjection ⁻¹' S := by
  change boundaryProjection (g • x)∈S ↔ boundaryProjection x∈S
  rw [boundaryProjection_smul]

theorem preimage_lineBase : boundaryProjection ⁻¹' lineBase=lineSide :=
  Set.ext boundaryProjection_mem_line

theorem preimage_planeBase : boundaryProjection ⁻¹' planeBase=planeSide :=
  Set.ext boundaryProjection_mem_plane

theorem preimage_cornerBase : boundaryProjection ⁻¹' cornerBase=cornerLocus :=
  Set.ext boundaryProjection_mem_corner

instance lineSideAction : MulAction principalSix lineSide where
  smul g x := ⟨g • x.val,lineSide_smul g x.property⟩
  one_smul x := Subtype.ext (one_smul principalSix x.val)
  mul_smul g h x := Subtype.ext (mul_smul g h x.val)

instance planeSideAction : MulAction principalSix planeSide where
  smul g x := ⟨g • x.val,planeSide_smul g x.property⟩
  one_smul x := Subtype.ext (one_smul principalSix x.val)
  mul_smul g h x := Subtype.ext (mul_smul g h x.val)

instance cornerLocusAction : MulAction principalSix cornerLocus where
  smul g x := ⟨g • x.val,⟨lineSide_smul g x.property.1,planeSide_smul g x.property.2⟩⟩
  one_smul x := Subtype.ext (one_smul principalSix x.val)
  mul_smul g h x := Subtype.ext (mul_smul g h x.val)

instance lineSideContinuous : ContinuousConstSMul principalSix lineSide :=
  ⟨fun g => ((continuous_const_smul g).comp continuous_subtype_val).subtype_mk _⟩
instance planeSideContinuous : ContinuousConstSMul principalSix planeSide :=
  ⟨fun g => ((continuous_const_smul g).comp continuous_subtype_val).subtype_mk _⟩
instance cornerLocusContinuous : ContinuousConstSMul principalSix cornerLocus :=
  ⟨fun g => ((continuous_const_smul g).comp continuous_subtype_val).subtype_mk _⟩

def lineInclusionHomotopyEquiv : ContinuousMap.HomotopyEquiv lineSide UpstairsLine :=
  (Homeomorph.setCongr preimage_lineBase).symm.toHomotopyEquiv.trans
    lineBaseRetraction.inclusionHomotopyEquiv

def planeInclusionHomotopyEquiv : ContinuousMap.HomotopyEquiv planeSide UpstairsPlane :=
  (Homeomorph.setCongr preimage_planeBase).symm.toHomotopyEquiv.trans
    planeBaseRetraction.inclusionHomotopyEquiv

def cornerInclusionHomotopyEquiv : ContinuousMap.HomotopyEquiv cornerLocus UpstairsOverlap :=
  (Homeomorph.setCongr preimage_cornerBase).symm.toHomotopyEquiv.trans
    cornerBaseRetraction.inclusionHomotopyEquiv

@[simp] theorem lineInclusion_val (x : lineSide) : (lineInclusionHomotopyEquiv x).val=x.val := rfl
@[simp] theorem planeInclusion_val (x : planeSide) : (planeInclusionHomotopyEquiv x).val=x.val := rfl
@[simp] theorem cornerInclusion_val (x : cornerLocus) : (cornerInclusionHomotopyEquiv x).val=x.val := rfl

def lineRetraction : C(UpstairsLine,lineSide) := lineInclusionHomotopyEquiv.invFun
def planeRetraction : C(UpstairsPlane,planeSide) := planeInclusionHomotopyEquiv.invFun
def cornerRetraction : C(UpstairsOverlap,cornerLocus) := cornerInclusionHomotopyEquiv.invFun

@[simp] theorem lineRetraction_val (x : UpstairsLine) : (lineRetraction x).val=lineBaseRetraction.lift (1,x) := rfl
@[simp] theorem planeRetraction_val (x : UpstairsPlane) : (planeRetraction x).val=planeBaseRetraction.lift (1,x) := rfl
@[simp] theorem cornerRetraction_val (x : UpstairsOverlap) : (cornerRetraction x).val=cornerBaseRetraction.lift (1,x) := rfl

theorem lineRetraction_equivariant (g : principalSix) (x : UpstairsLine) :
    lineRetraction (g • x)=g • lineRetraction x :=
  Subtype.ext (lineBaseRetraction.lift_equivariant g 1 x)

theorem planeRetraction_equivariant (g : principalSix) (x : UpstairsPlane) :
    planeRetraction (g • x)=g • planeRetraction x :=
  Subtype.ext (planeBaseRetraction.lift_equivariant g 1 x)

theorem cornerRetraction_equivariant (g : principalSix) (x : UpstairsOverlap) :
    cornerRetraction (g • x)=g • cornerRetraction x :=
  Subtype.ext (cornerBaseRetraction.lift_equivariant g 1 x)

theorem lineRetraction_fixed (x : UpstairsLine) (hx : x.val∈lineSide) : (lineRetraction x).val=x.val :=
  lineBaseRetraction.lift_fixed 1 x ((boundaryProjection_mem_line x.val).mpr hx)

theorem planeRetraction_fixed (x : UpstairsPlane) (hx : x.val∈planeSide) : (planeRetraction x).val=x.val :=
  planeBaseRetraction.lift_fixed 1 x ((boundaryProjection_mem_plane x.val).mpr hx)

theorem cornerRetraction_fixed (x : UpstairsOverlap) (hx : x.val∈cornerLocus) : (cornerRetraction x).val=x.val :=
  cornerBaseRetraction.lift_fixed 1 x ((boundaryProjection_mem_corner x.val).mpr hx)

end TernaryPoly.SymmetricSpaceBoundaryMV
