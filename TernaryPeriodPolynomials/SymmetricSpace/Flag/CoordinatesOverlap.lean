module

public import TernaryPeriodPolynomials.SymmetricSpace.Flag.CoordinatesCorner
public import TernaryPeriodPolynomials.SymmetricSpace.Flag.CoordinatesOverlapAlgebra
public import TernaryPeriodPolynomials.SymmetricSpace.Plane.BordificationTopology

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceFlagCoordinates
open SymmetricSpacePositive SymmetricSpaceParabolicCoordinates
open Topology Set

/-- The flag-to-plane overlap keeps the first simple root positive and allows the second to vanish. -/
def overlapDomain : Set Corner := {p | 0<p.2.1.val}
abbrev OverlapDomain := overlapDomain

theorem overlapDomain_open : IsOpen overlapDomain :=
  isOpen_lt continuous_const
    (continuous_subtype_val.comp (continuous_fst.comp continuous_snd))

/-- The actual trace-normalized positive binary shape in the overlap. -/
def overlapShape (p : OverlapDomain) : BinarySpace :=
  ⟨binaryNormalize (shapeMatrix (p.val.1 0) p.val.2.1.val),
    binaryNormalize_mem _ (shapeMatrix_positive _ _ p.property)⟩

/-- The full boundary overlap, defined also at the genuine face t2=0. -/
def planeOverlap (p : OverlapDomain) : SymmetricSpacePlaneBordification.PlaneBordification :=
  (![p.val.1 2,p.val.1 1],(overlapShape p,
    ⟨p.val.2.2.val/Real.sqrt (shapeTrace (p.val.1 0) p.val.2.1.val),
      div_nonneg p.val.2.2.property (Real.sqrt_nonneg _)⟩))

@[simp] theorem planeOverlap_unipotent (p : OverlapDomain) :
    (planeOverlap p).1=![p.val.1 2,p.val.1 1] := rfl

@[simp] theorem planeOverlap_shape (p : OverlapDomain) :
    (planeOverlap p).2.1.val=binaryNormalize (shapeMatrix (p.val.1 0) p.val.2.1.val) := rfl

@[simp] theorem planeOverlap_parameter (p : OverlapDomain) :
    (planeOverlap p).2.2.val=
      p.val.2.2.val/Real.sqrt (shapeTrace (p.val.1 0) p.val.2.1.val) := rfl

theorem continuous_overlap_matrix :
    Continuous (fun p : OverlapDomain => shapeMatrix (p.val.1 0) p.val.2.1.val) := by
  have hx : Continuous (fun p : OverlapDomain => p.val.1 0) := by fun_prop
  have ht : Continuous (fun p : OverlapDomain => p.val.2.1.val) := by fun_prop
  have hi : Continuous (fun p : OverlapDomain => (p.val.2.1.val^2)⁻¹) :=
    (ht.pow 2).inv₀ (fun p => pow_ne_zero 2 (ne_of_gt p.property))
  have hs : Continuous (fun p : OverlapDomain => (p.val.1 0)^2+(p.val.2.1.val^2)⁻¹) :=
    (hx.pow 2).add hi
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  fin_cases i <;> fin_cases j
  · simpa [shapeMatrix_formula] using hs
  · simpa [shapeMatrix_formula] using hx
  · simpa [shapeMatrix_formula] using hx
  · simpa [shapeMatrix_formula] using
      (continuous_const : Continuous (fun _ : OverlapDomain => (1 : ℝ)))

theorem continuous_overlapShape : Continuous overlapShape := by
  apply Continuous.subtype_mk
  exact (continuous_overlap_matrix.matrix_trace.inv₀ (fun p =>
    ne_of_gt (shapeMatrix_positive (p.val.1 0) p.val.2.1.val p.property).trace_pos)).smul
      continuous_overlap_matrix

/-- This continuous map is an actual extension of the interior coordinate overlap to t2=0. -/
theorem continuous_planeOverlap : Continuous planeOverlap := by
  apply Continuous.prodMk
  · fun_prop
  · apply Continuous.prodMk continuous_overlapShape
    apply Continuous.subtype_mk
    have htrace : Continuous (fun p : OverlapDomain => shapeTrace (p.val.1 0) p.val.2.1.val) := by
      simpa only [shapeMatrix_trace] using continuous_overlap_matrix.matrix_trace
    exact (show Continuous (fun p : OverlapDomain => p.val.2.2.val) by fun_prop).div₀ htrace.sqrt
      (fun p => ne_of_gt (Real.sqrt_pos.mpr (shapeTrace_pos _ _)))

/-- A positive root point lies in the actual flag-to-plane overlap domain. -/
def rootToOverlap (p : RootParameters) : OverlapDomain :=
  ⟨(positiveCornerHomeomorph p).val,p.2.1.property⟩

/-- Agreement with the exact plane embedding on every actual positive form in root coordinates. -/
theorem planeOverlap_root (p : RootParameters) :
    planeOverlap (rootToOverlap p)=
      SymmetricSpacePlaneBordification.embedding (rootHomeomorph.symm p) := by
  apply Prod.ext
  · exact (root_unipotent p).symm
  · apply Prod.ext
    · apply Subtype.ext
      exact (root_plane_shape p).symm
    · apply Subtype.ext
      exact (root_plane_parameter p).symm

/-- The two actual embeddings of Space agree through the explicit overlap map. -/
theorem planeOverlap_cornerEmbedding (S : Space) :
    planeOverlap ⟨cornerEmbedding S,(cornerHomeomorph S).property.1⟩=
      SymmetricSpacePlaneBordification.embedding S := by
  change planeOverlap (rootToOverlap (rootHomeomorph S))=_
  rw [planeOverlap_root,rootHomeomorph.symm_apply_apply]

/-- The t2=0 flag face maps exactly to the actual plane boundary. -/
theorem planeOverlap_boundary_iff (p : OverlapDomain) :
    planeOverlap p∈SymmetricSpacePlaneBordification.boundary ↔ p.val.2.2.val=0 := by
  change p.val.2.2.val/Real.sqrt (shapeTrace (p.val.1 0) p.val.2.1.val)=0 ↔ p.val.2.2.val=0
  rw [div_eq_zero_iff]
  simp [ne_of_gt (Real.sqrt_pos.mpr (shapeTrace_pos _ _))]

end TernaryPoly.SymmetricSpaceFlagCoordinates
