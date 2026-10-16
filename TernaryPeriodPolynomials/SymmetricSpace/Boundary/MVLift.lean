module

public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.MVBaseCover
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Homotopy.Equiv

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceBoundaryMV
open Topology SingularBoundaryRestriction IntegralGL3Congruence
open scoped unitInterval

/-- A genuine deformation onto a closed boundary piece, with its literal inclusion. -/
structure BaseRetraction (S A : Set BoundaryBase) where
  subset : A⊆S
  homotopy : C(I × S,BoundaryBase)
  zero : ∀ x : S,homotopy (0,x)=x.val
  preserves : ∀ (t : I) (x : S),homotopy (t,x)∈S
  fixed : ∀ (t : I) (x : S),x.val∈A → homotopy (t,x)=x.val
  endpoint : ∀ x : S,homotopy (1,x)∈A

def lineBaseRetraction : BaseRetraction lineNeighborhood lineBase :=
  ⟨lineBase_subset_neighborhood,lineBaseFlow,lineBaseFlow_zero,lineBaseFlow_preserves,
    lineBaseFlow_fixed,lineBaseFlow_endpoint⟩

def planeBaseRetraction : BaseRetraction planeNeighborhood planeBase :=
  ⟨planeBase_subset_neighborhood,planeBaseFlow,planeBaseFlow_zero,planeBaseFlow_preserves,
    planeBaseFlow_fixed,planeBaseFlow_endpoint⟩

def cornerBaseRetraction : BaseRetraction collarNeighborhood cornerBase :=
  ⟨cornerBase_subset_collar,cornerCollarFlow,collarFlow_zero _ _,collarFlow_preserves _ _,
    cornerCollarFlow_fixed,cornerCollarFlow_endpoint⟩

instance preimageAction (S : Set BoundaryBase) : MulAction principalSix (boundaryProjection ⁻¹' S) where
  smul g x := ⟨g • x.val,by change boundaryProjection (g • x.val)∈S; rw [boundaryProjection_smul]; exact x.property⟩
  one_smul x := Subtype.ext (one_smul _ _)
  mul_smul g h x := Subtype.ext (mul_smul _ _ _)

@[simp] theorem preimage_smul_val (S : Set BoundaryBase) (g : principalSix) (x : boundaryProjection ⁻¹' S) :
    (g • x).val=g • x.val := rfl

instance preimageContinuous (S : Set BoundaryBase) : ContinuousConstSMul principalSix (boundaryProjection ⁻¹' S) :=
  ⟨fun g => ((continuous_const_smul g).comp continuous_subtype_val).subtype_mk _⟩

namespace BaseRetraction
variable {S A : Set BoundaryBase} (D : BaseRetraction S A)

def pulledHomotopy : C(I × (boundaryProjection ⁻¹' S),BoundaryBase) :=
  ⟨fun z => D.homotopy (z.1,⟨boundaryProjection z.2.val,z.2.property⟩),
    D.homotopy.continuous.comp (continuous_fst.prodMk
      ((boundaryCovering.continuous.comp (continuous_subtype_val.comp continuous_snd)).subtype_mk _))⟩

/-- Actual covering-homotopy lift starting at the literal inclusion. -/
def lift : C(I × (boundaryProjection ⁻¹' S),BoundaryCover) :=
  boundaryCovering.liftHomotopy D.pulledHomotopy ⟨Subtype.val,continuous_subtype_val⟩
    (fun x => D.zero ⟨boundaryProjection x.val,x.property⟩)

@[simp] theorem lift_zero (x : boundaryProjection ⁻¹' S) : D.lift (0,x)=x.val :=
  boundaryCovering.liftHomotopy_zero _ _ _ x

theorem lift_projection (t : I) (x : boundaryProjection ⁻¹' S) :
    boundaryProjection (D.lift (t,x))=D.homotopy (t,⟨boundaryProjection x.val,x.property⟩) :=
  congr_fun (boundaryCovering.liftHomotopy_lifts _ _ _) (t,x)

theorem lift_preserves (t : I) (x : boundaryProjection ⁻¹' S) :
    D.lift (t,x)∈boundaryProjection ⁻¹' S := by
  change boundaryProjection (D.lift (t,x))∈S
  rw [D.lift_projection]
  exact D.preserves _ _

theorem lift_endpoint (x : boundaryProjection ⁻¹' S) :
    D.lift (1,x)∈boundaryProjection ⁻¹' A := by
  change boundaryProjection (D.lift (1,x))∈A
  rw [D.lift_projection]
  exact D.endpoint _

/-- Fixed downstairs points remain fixed upstairs by uniqueness of covering path lifts. -/
theorem lift_fixed (t : I) (x : boundaryProjection ⁻¹' S)
    (hx : x.val∈boundaryProjection ⁻¹' A) : D.lift (t,x)=x.val := by
  have he := boundaryCovering.eq_of_comp_eq
    (D.lift.continuous.comp (continuous_id.prodMk continuous_const)) continuous_const
    (g₁ := fun s : I => D.lift (s,x)) (g₂ := fun _ : I => x.val) ?_ 0 (D.lift_zero x)
  · exact congr_fun he t
  · funext s
    exact (D.lift_projection s x).trans (D.fixed s _ hx)

/-- The lift is principal-six equivariant; uniqueness compares the two lifted paths. -/
theorem lift_equivariant (g : principalSix) (t : I) (x : boundaryProjection ⁻¹' S) :
    D.lift (t,g • x)=g • D.lift (t,x) := by
  have he := boundaryCovering.eq_of_comp_eq
    (D.lift.continuous.comp (continuous_id.prodMk continuous_const))
    ((continuous_const_smul g).comp (D.lift.continuous.comp (continuous_id.prodMk continuous_const)))
    (g₁ := fun s : I => D.lift (s,g • x)) (g₂ := fun s : I => g • D.lift (s,x)) ?_ 0 ?_
  · exact congr_fun he t
  · funext s
    change boundaryProjection (D.lift (s,g • x))=boundaryProjection (g • D.lift (s,x))
    rw [boundaryProjection_smul,D.lift_projection,D.lift_projection]
    congr 1
    refine Prod.ext rfl ?_
    exact Subtype.ext (boundaryProjection_smul g x.val)
  · rw [D.lift_zero,D.lift_zero]
    rfl

def selfLift : C(I × (boundaryProjection ⁻¹' S),(boundaryProjection ⁻¹' S)) :=
  ⟨fun z => ⟨D.lift z,D.lift_preserves z.1 z.2⟩,D.lift.continuous.subtype_mk _⟩

def retraction : C((boundaryProjection ⁻¹' S),(boundaryProjection ⁻¹' A)) :=
  ⟨fun x => ⟨D.lift (1,x),D.lift_endpoint x⟩,
    (D.lift.continuous.comp (continuous_const.prodMk continuous_id)).subtype_mk _⟩

def inclusion : C((boundaryProjection ⁻¹' A),(boundaryProjection ⁻¹' S)) :=
  ⟨Set.inclusion (Set.preimage_mono D.subset),continuous_inclusion _⟩

@[simp] theorem retraction_inclusion (x : boundaryProjection ⁻¹' A) :
    D.retraction (D.inclusion x)=x :=
  Subtype.ext (D.lift_fixed 1 (D.inclusion x) x.property)

theorem retraction_equivariant (g : principalSix) (x : boundaryProjection ⁻¹' S) :
    D.retraction (g • x)=g • D.retraction x :=
  Subtype.ext (D.lift_equivariant g 1 x)

def inclusionHomotopyEquiv : ContinuousMap.HomotopyEquiv
    (boundaryProjection ⁻¹' A) (boundaryProjection ⁻¹' S) where
  toFun := D.inclusion
  invFun := D.retraction
  left_inv := by
    refine ⟨⟨⟨fun z => z.2,continuous_snd⟩,?_,?_⟩⟩
    · intro x
      exact (D.retraction_inclusion x).symm
    · intro _
      rfl
  right_inv := by
    apply Nonempty.intro
    apply ContinuousMap.Homotopy.symm
    refine ⟨D.selfLift,?_,?_⟩
    · intro x
      exact Subtype.ext (D.lift_zero x)
    · intro _
      rfl

end BaseRetraction
end TernaryPoly.SymmetricSpaceBoundaryMV
