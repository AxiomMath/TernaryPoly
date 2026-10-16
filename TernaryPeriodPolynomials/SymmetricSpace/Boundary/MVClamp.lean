module

public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.MVSides
public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.MVOpenGlue
public import Mathlib.Analysis.Convex.Basic

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceBoundaryMV
open Topology SingularBoundaryRestriction
open scoped unitInterval

abbrev NormalInterval := Set.Ioo (-collarRadius) collarRadius

variable (r : C(ℝ,ℝ)) (hr : Set.MapsTo r NormalInterval NormalInterval)

def stripFlow : C(I × CollarStrip,CollarStrip) :=
  ⟨fun z => ⟨(z.2.val.1,(1-z.1.val)*z.2.val.2+z.1.val*r z.2.val.2),
    ⟨Set.mem_univ _, by
      exact (convex_Ioo (-collarRadius) collarRadius) z.2.property.2 (hr z.2.property.2)
        (sub_nonneg.mpr z.1.property.2) z.1.property.1 (sub_add_cancel 1 z.1.val)⟩⟩,
    ((continuous_fst.comp (continuous_subtype_val.comp continuous_snd)).prodMk
      (((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
        (continuous_snd.comp (continuous_subtype_val.comp continuous_snd))).add
      ((continuous_subtype_val.comp continuous_fst).mul
        (r.continuous.comp (continuous_snd.comp (continuous_subtype_val.comp continuous_snd)))))).subtype_mk _⟩

@[simp] theorem stripFlow_zero (x : CollarStrip) : stripFlow r hr (0,x)=x := by
  apply Subtype.ext
  change (x.val.1,(1-(0:ℝ))*x.val.2+(0:ℝ)*r x.val.2)=x.val
  simp

@[simp] theorem stripFlow_one_val (x : CollarStrip) :
    (stripFlow r hr (1,x)).val=(x.val.1,r x.val.2) := by
  change (x.val.1,(1-(1:ℝ))*x.val.2+(1:ℝ)*r x.val.2)=_
  simp

theorem stripFlow_fixed (t : I) (x : CollarStrip) (hx : r x.val.2=x.val.2) :
    stripFlow r hr (t,x)=x := by
  apply Subtype.ext
  change (x.val.1,(1-t.val)*x.val.2+t.val*r x.val.2)=x.val
  rw [hx]
  congr 1
  ring

def collarFlow : C(I × collarNeighborhood,BoundaryBase) :=
  ⟨fun z => collarParam (stripFlow r hr (z.1,collarHomeomorph.symm z.2)),
    collarParam_isOpenEmbedding.continuous.comp ((stripFlow r hr).continuous.comp
      (continuous_fst.prodMk (collarHomeomorph.symm.continuous.comp continuous_snd)))⟩

@[simp] theorem collarFlow_zero (x : collarNeighborhood) : collarFlow r hr (0,x)=x.val := by
  change collarParam (stripFlow r hr (0,collarHomeomorph.symm x))=x.val
  rw [stripFlow_zero]
  exact congrArg Subtype.val (collarHomeomorph.apply_symm_apply x)

theorem collarFlow_preserves (t : I) (x : collarNeighborhood) : collarFlow r hr (t,x)∈collarNeighborhood :=
  ⟨_,rfl⟩

theorem collarFlow_fixed (t : I) (x : collarNeighborhood)
    (hx : r (collarHomeomorph.symm x).val.2=(collarHomeomorph.symm x).val.2) :
    collarFlow r hr (t,x)=x.val := by
  change collarParam (stripFlow r hr (t,collarHomeomorph.symm x))=x.val
  rw [stripFlow_fixed r hr t _ hx]
  exact congrArg Subtype.val (collarHomeomorph.apply_symm_apply x)

def lineClamp : C(ℝ,ℝ) := ⟨fun s => max s 0,continuous_id.max continuous_const⟩
def planeClamp : C(ℝ,ℝ) := ⟨fun s => min s 0,continuous_id.min continuous_const⟩
def cornerClamp : C(ℝ,ℝ) := ContinuousMap.const ℝ 0

theorem lineClamp_maps : Set.MapsTo lineClamp NormalInterval NormalInterval := by
  intro s hs
  exact ⟨lt_max_of_lt_left hs.1,max_lt hs.2 collarRadius_pos⟩

theorem planeClamp_maps : Set.MapsTo planeClamp NormalInterval NormalInterval := by
  intro s hs
  exact ⟨lt_min hs.1 (by linarith [collarRadius_pos]),min_lt_of_left_lt hs.2⟩

theorem cornerClamp_maps : Set.MapsTo cornerClamp NormalInterval NormalInterval := by
  intro _ _
  exact ⟨by change -collarRadius<0; linarith [collarRadius_pos],collarRadius_pos⟩

def lineCollarFlow := collarFlow lineClamp lineClamp_maps
def planeCollarFlow := collarFlow planeClamp planeClamp_maps
def cornerCollarFlow := collarFlow cornerClamp cornerClamp_maps

theorem collarCoordinate_line (x : collarNeighborhood) :
    x.val∈lineBase ↔ 0≤(collarHomeomorph.symm x).val.2 := by
  rw [←collarParam_line]
  exact Iff.of_eq (congrArg (fun y => y∈lineBase)
    (congrArg Subtype.val (collarHomeomorph.apply_symm_apply x)).symm)

theorem collarCoordinate_plane (x : collarNeighborhood) :
    x.val∈planeBase ↔ (collarHomeomorph.symm x).val.2≤0 := by
  rw [←collarParam_plane]
  exact Iff.of_eq (congrArg (fun y => y∈planeBase)
    (congrArg Subtype.val (collarHomeomorph.apply_symm_apply x)).symm)

theorem collarCoordinate_corner (x : collarNeighborhood) :
    x.val∈cornerBase ↔ (collarHomeomorph.symm x).val.2=0 := by
  rw [←collarParam_corner]
  exact Iff.of_eq (congrArg (fun y => y∈cornerBase)
    (congrArg Subtype.val (collarHomeomorph.apply_symm_apply x)).symm)

theorem lineCollarFlow_fixed (t : I) (x : collarNeighborhood) (hx : x.val∈lineBase) :
    lineCollarFlow (t,x)=x.val :=
  collarFlow_fixed _ _ t x (max_eq_left ((collarCoordinate_line x).mp hx))

theorem planeCollarFlow_fixed (t : I) (x : collarNeighborhood) (hx : x.val∈planeBase) :
    planeCollarFlow (t,x)=x.val :=
  collarFlow_fixed _ _ t x (min_eq_left ((collarCoordinate_plane x).mp hx))

theorem cornerCollarFlow_fixed (t : I) (x : collarNeighborhood) (hx : x.val∈cornerBase) :
    cornerCollarFlow (t,x)=x.val :=
  collarFlow_fixed _ _ t x ((collarCoordinate_corner x).mp hx).symm

theorem lineCollarFlow_endpoint (x : collarNeighborhood) : lineCollarFlow (1,x)∈lineBase := by
  change collarParam (stripFlow lineClamp lineClamp_maps (1,collarHomeomorph.symm x))∈lineBase
  rw [collarParam_line,stripFlow_one_val]
  exact le_max_right _ _

theorem planeCollarFlow_endpoint (x : collarNeighborhood) : planeCollarFlow (1,x)∈planeBase := by
  change collarParam (stripFlow planeClamp planeClamp_maps (1,collarHomeomorph.symm x))∈planeBase
  rw [collarParam_plane,stripFlow_one_val]
  exact min_le_right _ _

theorem cornerCollarFlow_endpoint (x : collarNeighborhood) : cornerCollarFlow (1,x)∈cornerBase := by
  change collarParam (stripFlow cornerClamp cornerClamp_maps (1,collarHomeomorph.symm x))∈cornerBase
  rw [collarParam_corner,stripFlow_one_val]
  rfl

end TernaryPoly.SymmetricSpaceBoundaryMV
