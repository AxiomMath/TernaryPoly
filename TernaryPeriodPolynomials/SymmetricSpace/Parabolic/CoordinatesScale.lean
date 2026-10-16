module

public import TernaryPeriodPolynomials.SymmetricSpace.Parabolic.CoordinatesHomeomorph

@[expose] public section

open Matrix
noncomputable section
namespace TernaryPoly.SymmetricSpaceParabolicCoordinates
open SymmetricSpacePositive

/-- The actual trace-one binary positive-form space. -/
def binaryTraceOnePositive : Set Mat2 := {B | B.PosDef ∧ B.trace=1}
abbrev BinarySpace := binaryTraceOnePositive
abbrev PositiveScale := Set.Ioi (0 : ℝ)

def binaryNormalize (B : Mat2) : Mat2 := B.trace⁻¹ • B

theorem binaryNormalize_mem (B : Mat2) (hB : B.PosDef) :
    binaryNormalize B∈binaryTraceOnePositive := by
  refine ⟨hB.smul (inv_pos.mpr hB.trace_pos),?_⟩
  rw [binaryNormalize,trace_smul,smul_eq_mul,inv_mul_cancel₀ (ne_of_gt hB.trace_pos)]

/-- Positive binary forms split into their exact trace-one shape and positive trace scale. -/
def shapeScaleHomeomorph : PosDef2 ≃ₜ (BinarySpace × PositiveScale) where
  toFun B := (⟨binaryNormalize B.val,binaryNormalize_mem B.val B.property⟩,
    ⟨B.val.trace,B.property.trace_pos⟩)
  invFun p := ⟨p.2.val • p.1.val,p.1.property.1.smul p.2.property⟩
  left_inv B := by
    apply Subtype.ext
    change B.val.trace • (B.val.trace⁻¹ • B.val)=B.val
    rw [smul_smul,mul_inv_cancel₀ (ne_of_gt B.property.trace_pos),one_smul]
  right_inv p := by
    apply Prod.ext
    · apply Subtype.ext
      change binaryNormalize (p.2.val • p.1.val)=p.1.val
      rw [binaryNormalize,trace_smul,p.1.property.2,smul_eq_mul,mul_one,
        smul_smul,inv_mul_cancel₀ (ne_of_gt p.2.property),one_smul]
    · apply Subtype.ext
      change (p.2.val • p.1.val).trace=p.2.val
      rw [trace_smul,p.1.property.2,smul_eq_mul,mul_one]
  continuous_toFun := by
    have hval : Continuous (fun B : PosDef2 => B.val) := continuous_subtype_val
    apply Continuous.prodMk
    · apply Continuous.subtype_mk
      exact (hval.matrix_trace.inv₀ (fun B => ne_of_gt B.property.trace_pos)).smul hval
    · exact Continuous.subtype_mk hval.matrix_trace _
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact (continuous_subtype_val.comp continuous_snd).smul
      (continuous_subtype_val.comp continuous_fst)

@[simp] theorem shapeScaleHomeomorph_shape (B : PosDef2) :
    (shapeScaleHomeomorph B).1.val=binaryNormalize B.val := rfl

@[simp] theorem shapeScaleHomeomorph_scale (B : PosDef2) :
    (shapeScaleHomeomorph B).2.val=B.val.trace := rfl

@[simp] theorem shapeScaleHomeomorph_symm (p : BinarySpace × PositiveScale) :
    (shapeScaleHomeomorph.symm p).val=p.2.val • p.1.val := rfl

/-- The complete explicit plane-parabolic product: unipotent vector, binary shape, positive scale. -/
def fullHorosphericalHomeomorph : Space ≃ₜ (Vec2 × (BinarySpace × PositiveScale)) :=
  horosphericalHomeomorph.trans ((Homeomorph.refl Vec2).prodCongr shapeScaleHomeomorph)

@[simp] theorem fullHorosphericalHomeomorph_unipotent (S : Space) :
    (fullHorosphericalHomeomorph S).1=unipotent S.val := rfl

@[simp] theorem fullHorosphericalHomeomorph_shape (S : Space) :
    (fullHorosphericalHomeomorph S).2.1.val=binaryNormalize (schur S.val) := rfl

@[simp] theorem fullHorosphericalHomeomorph_scale (S : Space) :
    (fullHorosphericalHomeomorph S).2.2.val=(schur S.val).trace := rfl

@[simp] theorem fullHorosphericalHomeomorph_symm (p : Vec2 × (BinarySpace × PositiveScale)) :
    (fullHorosphericalHomeomorph.symm p).val=normalize (assemble p.1 (p.2.2.val • p.2.1.val)) := rfl

end TernaryPoly.SymmetricSpaceParabolicCoordinates
