module

public import TernaryPeriodPolynomials.SymmetricSpace.Flag.PlaneHomeomorphAlgebra

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceFlagPlaneHomeomorph
open SymmetricSpacePositive SymmetricSpaceParabolicCoordinates SymmetricSpaceFlagCoordinates
open SymmetricSpacePlaneBordification

/-- The inverse flag coordinates of every point of the entire plane partial bordification. -/
def inverse (p : PlaneBordification) : OverlapDomain :=
  ⟨(![binaryX p.2.1.val,p.1 1,p.1 0],
    (⟨shapeRoot p.2.1,show (0 : ℝ)≤shapeRoot p.2.1 from (shapeRoot_pos p.2.1).le⟩,
      ⟨p.2.2.val/Real.sqrt (p.2.1.val 1 1),by
        change 0≤p.2.2.val/Real.sqrt (p.2.1.val 1 1)
        exact div_nonneg p.2.2.property (Real.sqrt_nonneg _)⟩)),shapeRoot_pos p.2.1⟩

theorem planeOverlap_inverse (p : PlaneBordification) : planeOverlap (inverse p)=p := by
  apply Prod.ext
  · ext i; fin_cases i <;> rfl
  · apply Prod.ext
    · exact shapePoint_reconstruct p.2.1
    · apply Subtype.ext
      change p.2.2.val/Real.sqrt (p.2.1.val 1 1)/
        Real.sqrt (shapeTrace (binaryX p.2.1.val) (shapeRoot p.2.1))=p.2.2.val
      rw [shapeTrace_reconstruct,Real.sqrt_inv]
      field_simp [ne_of_gt (Real.sqrt_pos.mpr p.2.1.property.1.diag_pos)]

theorem inverse_planeOverlap (p : OverlapDomain) : inverse (planeOverlap p)=p := by
  have hp : 0<p.val.2.1.val := p.property
  apply Subtype.ext
  apply Prod.ext
  · ext i
    fin_cases i
    · exact shapePoint_x (p.val.1 0) p.val.2.1.val p.property
    · rfl
    · rfl
  · apply Prod.ext
    · apply Subtype.ext
      exact shapePoint_root (p.val.1 0) p.val.2.1.val p.property
    · apply Subtype.ext
      change (p.val.2.2.val/Real.sqrt (shapeTrace (p.val.1 0) p.val.2.1.val))/
        Real.sqrt ((shapePoint (p.val.1 0) p.val.2.1.val hp).val 1 1)=p.val.2.2.val
      rw [shapePoint_11,Real.sqrt_inv]
      field_simp [ne_of_gt (Real.sqrt_pos.mpr (shapeTrace_pos _ _))]

theorem continuous_inverse : Continuous inverse := by
  have hT : Continuous (fun p : PlaneBordification => p.2.1) := continuous_fst.comp continuous_snd
  have hb : Continuous (fun p : PlaneBordification => p.2.1.val 1 1) :=
    (continuous_subtype_val.comp hT).matrix_elem 1 1
  have hx : Continuous (fun p : PlaneBordification => binaryX p.2.1.val) :=
    ((continuous_subtype_val.comp hT).matrix_elem 0 1).div₀ hb
      (fun p => ne_of_gt p.2.1.property.1.diag_pos)
  have hr := continuous_shapeRoot.comp hT
  have ht : Continuous (fun p : PlaneBordification => p.2.2.val/Real.sqrt (p.2.1.val 1 1)) :=
    continuous_parameter.div₀ hb.sqrt (fun p => ne_of_gt (Real.sqrt_pos.mpr p.2.1.property.1.diag_pos))
  apply Continuous.subtype_mk
  apply Continuous.prodMk
  · apply continuous_pi
    intro i
    fin_cases i
    · exact hx
    · fun_prop
    · fun_prop
  · exact (hr.subtype_mk _).prodMk (ht.subtype_mk _)

/-- The actual overlap is a homeomorphism onto the entire plane partial bordification. -/
def planeOverlapHomeomorph : OverlapDomain ≃ₜ PlaneBordification where
  toFun := planeOverlap
  invFun := inverse
  left_inv := inverse_planeOverlap
  right_inv := planeOverlap_inverse
  continuous_toFun := continuous_planeOverlap
  continuous_invFun := continuous_inverse

@[simp] theorem planeOverlapHomeomorph_apply (p : OverlapDomain) :
    planeOverlapHomeomorph p=planeOverlap p := rfl

@[simp] theorem planeOverlapHomeomorph_symm_coordinates (p : PlaneBordification) :
    ((planeOverlapHomeomorph.symm p).val.1,
      (planeOverlapHomeomorph.symm p).val.2.1.val,
      (planeOverlapHomeomorph.symm p).val.2.2.val)=
    (![p.2.1.val 0 1/p.2.1.val 1 1,p.1 1,p.1 0],
      p.2.1.val 1 1/Real.sqrt p.2.1.val.det,p.2.2.val/Real.sqrt (p.2.1.val 1 1)) := rfl

theorem planeOverlapHomeomorph_embedding (S : Space) :
    planeOverlapHomeomorph ⟨cornerEmbedding S,(cornerHomeomorph S).property.1⟩=embedding S :=
  planeOverlap_cornerEmbedding S

theorem planeOverlapHomeomorph_boundary_iff (p : OverlapDomain) :
    planeOverlapHomeomorph p∈boundary ↔ p.val.2.2.val=0 := planeOverlap_boundary_iff p

theorem planeOverlapHomeomorph_interior_iff (p : OverlapDomain) :
    planeOverlapHomeomorph p∈interior ↔ 0<p.val.2.2.val := by
  change 0<p.val.2.2.val/Real.sqrt (shapeTrace (p.val.1 0) p.val.2.1.val) ↔ 0<p.val.2.2.val
  exact div_pos_iff_of_pos_right (Real.sqrt_pos.mpr (shapeTrace_pos _ _))

end TernaryPoly.SymmetricSpaceFlagPlaneHomeomorph
