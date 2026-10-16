module

public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.MVUpstairs

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceBoundaryMV
open Topology SingularBoundaryRestriction IntegralGL3Congruence
open scoped unitInterval

def overlapToLine : C(UpstairsOverlap,UpstairsLine) :=
  ⟨Set.inclusion (fun _ h => Or.inr h),continuous_inclusion _⟩
def overlapToPlane : C(UpstairsOverlap,UpstairsPlane) :=
  ⟨Set.inclusion (fun _ h => Or.inr h),continuous_inclusion _⟩
def cornerToLine : C(cornerLocus,lineSide) :=
  ⟨Set.inclusion (fun _ h => h.1),continuous_inclusion _⟩
def cornerToPlane : C(cornerLocus,planeSide) :=
  ⟨Set.inclusion (fun _ h => h.2),continuous_inclusion _⟩

/-- Compatibility is the lifted corner contraction followed by the actual line retraction. -/
def lineCompatibility : ContinuousMap.Homotopy
    (lineRetraction.comp overlapToLine) (cornerToLine.comp cornerRetraction) where
  toFun z := lineRetraction (overlapToLine (cornerBaseRetraction.selfLift z))
  continuous_toFun := lineRetraction.continuous.comp
    (overlapToLine.continuous.comp cornerBaseRetraction.selfLift.continuous)
  map_zero_left x := by
    exact congrArg (fun y => lineRetraction (overlapToLine y))
      (show cornerBaseRetraction.selfLift (0,x)=x from
        Subtype.ext (cornerBaseRetraction.lift_zero x))
  map_one_left x := by
    apply Subtype.ext
    exact lineRetraction_fixed _ (cornerRetraction x).property.1

def planeCompatibility : ContinuousMap.Homotopy
    (planeRetraction.comp overlapToPlane) (cornerToPlane.comp cornerRetraction) where
  toFun z := planeRetraction (overlapToPlane (cornerBaseRetraction.selfLift z))
  continuous_toFun := planeRetraction.continuous.comp
    (overlapToPlane.continuous.comp cornerBaseRetraction.selfLift.continuous)
  map_zero_left x := by
    exact congrArg (fun y => planeRetraction (overlapToPlane y))
      (show cornerBaseRetraction.selfLift (0,x)=x from
        Subtype.ext (cornerBaseRetraction.lift_zero x))
  map_one_left x := by
    apply Subtype.ext
    exact planeRetraction_fixed _ (cornerRetraction x).property.2

theorem BaseRetraction.selfLift_equivariant {S A : Set BoundaryBase} (D : BaseRetraction S A)
    (g : principalSix) (t : I) (x : boundaryProjection ⁻¹' S) :
    D.selfLift (t,g • x)=g • D.selfLift (t,x) :=
  Subtype.ext (D.lift_equivariant g t x)

theorem lineCompatibility_equivariant (g : principalSix) (t : I) (x : UpstairsOverlap) :
    lineCompatibility (t,g • x)=g • lineCompatibility (t,x) := by
  change lineRetraction (overlapToLine (cornerBaseRetraction.selfLift (t,g • x)))=_
  rw [BaseRetraction.selfLift_equivariant]
  change lineRetraction (g • overlapToLine (cornerBaseRetraction.selfLift (t,x)))=_
  rw [lineRetraction_equivariant]
  rfl

theorem planeCompatibility_equivariant (g : principalSix) (t : I) (x : UpstairsOverlap) :
    planeCompatibility (t,g • x)=g • planeCompatibility (t,x) := by
  change planeRetraction (overlapToPlane (cornerBaseRetraction.selfLift (t,g • x)))=_
  rw [BaseRetraction.selfLift_equivariant]
  change planeRetraction (g • overlapToPlane (cornerBaseRetraction.selfLift (t,x)))=_
  rw [planeRetraction_equivariant]
  rfl

end TernaryPoly.SymmetricSpaceBoundaryMV
