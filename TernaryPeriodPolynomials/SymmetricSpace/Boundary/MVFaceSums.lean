module

public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.MVCompatibility
public import Mathlib.Algebra.Group.Action.TransferInstance

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceBoundaryMV
open Topology OrdinaryIncidence SymmetricSpaceRationalGluing SymmetricSpaceBoundaryFaces
  SymmetricSpaceBoundaryFaceTopology SingularBoundaryRestriction IntegralGL3Congruence

namespace DisjointClosedUnion
variable {X ι : Type*} [TopologicalSpace X] (F : ι → Set X)
variable (hloc : LocallyFinite F) (hclosed : ∀ i,IsClosed (F i))
variable (huniq : ∀ {i j : ι} {x : X},x∈F i → x∈F j → i=j)

def totalMap : (Σ i,F i) → (⋃ i,F i) := fun x => ⟨x.2.val,Set.mem_iUnion.mpr ⟨x.1,x.2.property⟩⟩

include huniq in
omit [TopologicalSpace X] in
theorem totalMap_bijective : Function.Bijective (totalMap F) := by
  constructor
  · rintro ⟨i,x⟩ ⟨j,y⟩ he
    have hv := congrArg Subtype.val he
    have hi : i=j := huniq x.property (hv ▸ y.property)
    subst j
    exact congrArg (Sigma.mk i) (Subtype.ext hv)
  · rintro ⟨x,hx⟩
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hx
    exact ⟨⟨i,⟨x,hi⟩⟩,rfl⟩

include hloc hclosed huniq in
theorem piece_open (i : ι) : IsOpen (Subtype.val ⁻¹' F i : Set (⋃ j,F j)) := by
  let B : Set X := ⋃ j : {j : ι | j≠i},F j.val
  have hB : IsClosed B := (hloc.comp_injective Subtype.val_injective).isClosed_iUnion (fun j => hclosed j.val)
  have he : (Subtype.val ⁻¹' F i : Set (⋃ j,F j))=(Subtype.val ⁻¹' B)ᶜ := by
    ext x
    constructor
    · intro hx hB
      obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hB
      exact j.property (huniq hj hx)
    · intro hx
      obtain ⟨j,hj⟩ := Set.mem_iUnion.mp x.property
      by_cases he : j=i
      · exact he ▸ hj
      · exact False.elim (hx (Set.mem_iUnion.mpr ⟨⟨j,he⟩,hj⟩))
  rw [he]
  exact (hB.preimage continuous_subtype_val).isOpen_compl

def homeomorph : (Σ i,F i) ≃ₜ (⋃ i,F i) :=
  (Equiv.ofBijective (totalMap F) (totalMap_bijective F huniq)).toHomeomorphOfContinuousOpen
    (continuous_sigma (fun _ => continuous_subtype_val.subtype_mk _))
    (isOpenMap_sigma.mpr (fun i =>
      (IsOpenEmbedding.inclusion (fun _ hx => Set.mem_iUnion.mpr ⟨i,hx⟩)
        (piece_open F hloc hclosed huniq i)).isOpenMap))

end DisjointClosedUnion

/-- A subset already contained in the actual boundary has its unchanged subspace topology. -/
def boundarySubsetHomeomorph (F : Set Glued) (hF : F⊆upstairsBoundary) :
    F ≃ₜ (Subtype.val ⁻¹' F : Set BoundaryCover) where
  toFun x := ⟨⟨x.val,hF x.property⟩,x.property⟩
  invFun x := ⟨x.val.val,x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

abbrev LineFaceSum := Σ L : Line,lineFace L
abbrev PlaneFaceSum := Σ P : Plane,planeFace P
abbrev CornerFaceSum := Σ F : Flag,flagFace F

def lineFaceSumHomeomorph : LineFaceSum ≃ₜ lineSide :=
  (DisjointClosedUnion.homeomorph lineFace lineFaces_locallyFinite lineFace_closed
    (fun h h' => lineFace_unique h h')).trans
    (boundarySubsetHomeomorph _ (by
      intro x hx
      obtain ⟨L,hL⟩ := Set.mem_iUnion.mp hx
      exact (boundary_iff_faces x).mpr (Or.inl ⟨L,hL⟩)))

def planeFaceSumHomeomorph : PlaneFaceSum ≃ₜ planeSide :=
  (DisjointClosedUnion.homeomorph planeFace planeFaces_locallyFinite planeFace_closed
    (fun h h' => planeFace_unique h h')).trans
    (boundarySubsetHomeomorph _ (by
      intro x hx
      obtain ⟨P,hP⟩ := Set.mem_iUnion.mp hx
      exact (boundary_iff_faces x).mpr (Or.inr ⟨P,hP⟩)))

def cornerFaceSumHomeomorph : CornerFaceSum ≃ₜ cornerLocus :=
  (DisjointClosedUnion.homeomorph flagFace flagFaces_locallyFinite flagFace_closed
    (fun h h' => flagFace_unique h h')).trans
    ((boundarySubsetHomeomorph _ (fun _ h => allCorners_mem_boundary h)).trans
      (Homeomorph.setCongr cornerLocus_eq_preimage.symm))

@[simp] theorem lineFaceSumHomeomorph_val (x : LineFaceSum) :
    (lineFaceSumHomeomorph x).val.val=x.2.val := rfl
@[simp] theorem planeFaceSumHomeomorph_val (x : PlaneFaceSum) :
    (planeFaceSumHomeomorph x).val.val=x.2.val := rfl
@[simp] theorem cornerFaceSumHomeomorph_val (x : CornerFaceSum) :
    (cornerFaceSumHomeomorph x).val.val=x.2.val := rfl

/-- These transported actions are the actual arithmetic action on the disjoint entire faces. -/
instance lineFaceSumAction : MulAction principalSix LineFaceSum := lineFaceSumHomeomorph.toEquiv.mulAction _
instance planeFaceSumAction : MulAction principalSix PlaneFaceSum := planeFaceSumHomeomorph.toEquiv.mulAction _
instance cornerFaceSumAction : MulAction principalSix CornerFaceSum := cornerFaceSumHomeomorph.toEquiv.mulAction _

theorem lineFaceSumHomeomorph_equivariant (g : principalSix) (x : LineFaceSum) :
    lineFaceSumHomeomorph (g • x)=g • lineFaceSumHomeomorph x :=
  lineFaceSumHomeomorph.apply_symm_apply _
theorem planeFaceSumHomeomorph_equivariant (g : principalSix) (x : PlaneFaceSum) :
    planeFaceSumHomeomorph (g • x)=g • planeFaceSumHomeomorph x :=
  planeFaceSumHomeomorph.apply_symm_apply _
theorem cornerFaceSumHomeomorph_equivariant (g : principalSix) (x : CornerFaceSum) :
    cornerFaceSumHomeomorph (g • x)=g • cornerFaceSumHomeomorph x :=
  cornerFaceSumHomeomorph.apply_symm_apply _

/-- On underlying geometric points the sum action is literally the original arithmetic action. -/
theorem lineFaceSum_smul_val (g : principalSix) (x : LineFaceSum) : (g • x).2.val=g • x.2.val :=
  congrArg (fun y : lineSide => y.val.val) (lineFaceSumHomeomorph_equivariant g x)
theorem planeFaceSum_smul_val (g : principalSix) (x : PlaneFaceSum) : (g • x).2.val=g • x.2.val :=
  congrArg (fun y : planeSide => y.val.val) (planeFaceSumHomeomorph_equivariant g x)
theorem cornerFaceSum_smul_val (g : principalSix) (x : CornerFaceSum) : (g • x).2.val=g • x.2.val :=
  congrArg (fun y : cornerLocus => y.val.val) (cornerFaceSumHomeomorph_equivariant g x)

def lineFaceSumEquiv : ContinuousMap.HomotopyEquiv LineFaceSum UpstairsLine :=
  lineFaceSumHomeomorph.toHomotopyEquiv.trans lineInclusionHomotopyEquiv
def planeFaceSumEquiv : ContinuousMap.HomotopyEquiv PlaneFaceSum UpstairsPlane :=
  planeFaceSumHomeomorph.toHomotopyEquiv.trans planeInclusionHomotopyEquiv
def cornerFaceSumEquiv : ContinuousMap.HomotopyEquiv CornerFaceSum UpstairsOverlap :=
  cornerFaceSumHomeomorph.toHomotopyEquiv.trans cornerInclusionHomotopyEquiv

end TernaryPoly.SymmetricSpaceBoundaryMV
