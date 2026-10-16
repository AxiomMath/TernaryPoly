module

public import TernaryPeriodPolynomials.SymmetricSpace.Flag.CoordinatesOverlap

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceFlagPlaneHomeomorph
open Matrix
open SymmetricSpaceParabolicCoordinates SymmetricSpaceFlagCoordinates

/-- The positive root recovered directly from a trace-one binary form. -/
def shapeRoot (T : BinarySpace) : ℝ := T.val 1 1 / Real.sqrt T.val.det

theorem shapeRoot_pos (T : BinarySpace) : 0<shapeRoot T :=
  div_pos T.property.1.diag_pos (Real.sqrt_pos.mpr T.property.1.det_pos)

def shapePoint (x t : ℝ) (ht : 0<t) : BinarySpace :=
  ⟨binaryNormalize (shapeMatrix x t),binaryNormalize_mem _ (shapeMatrix_positive x t ht)⟩

@[simp] theorem shapePoint_11 (x t : ℝ) (ht : 0<t) :
    (shapePoint x t ht).val 1 1=(shapeTrace x t)⁻¹ := by
  simp [shapePoint,binaryNormalize,shapeMatrix_formula,shapeTrace]

@[simp] theorem shapePoint_x (x t : ℝ) (ht : 0<t) :
    binaryX (shapePoint x t ht).val=x := by
  have hh : x^2+(t^2)⁻¹+1≠0 := ne_of_gt (shapeTrace_pos x t)
  simp [binaryX,shapePoint,binaryNormalize,shapeMatrix_formula]
  field_simp [hh]

theorem shapePoint_det (x t : ℝ) (ht : 0<t) :
    (shapePoint x t ht).val.det=((shapeTrace x t)⁻¹*t⁻¹)^2 := by
  simp [shapePoint,binaryNormalize,Matrix.det_fin_two,shapeMatrix_formula,shapeTrace]
  ring

@[simp] theorem shapePoint_root (x t : ℝ) (ht : 0<t) :
    shapeRoot (shapePoint x t ht)=t := by
  rw [shapeRoot,shapePoint_11,shapePoint_det,Real.sqrt_sq
    (mul_nonneg (inv_nonneg.mpr (shapeTrace_pos x t).le) (inv_nonneg.mpr ht.le))]
  field_simp [ne_of_gt (shapeTrace_pos x t),ne_of_gt ht]

theorem shapeRoot_inv_sq (T : BinarySpace) :
    (shapeRoot T ^2)⁻¹=T.val.det/(T.val 1 1)^2 := by
  have hb : T.val 1 1≠0 := ne_of_gt T.property.1.diag_pos
  have hd : T.val.det≠0 := ne_of_gt T.property.1.det_pos
  simp only [shapeRoot,div_pow,Real.sq_sqrt T.property.1.det_pos.le]
  field_simp

/-- The recovered shear and root reconstruct the exact original form up to its bottom pivot. -/
theorem shapeMatrix_reconstruct (T : BinarySpace) :
    shapeMatrix (binaryX T.val) (shapeRoot T)=(T.val 1 1)⁻¹ • T.val := by
  have hb : T.val 1 1≠0 := ne_of_gt T.property.1.diag_pos
  have hs : T.val 1 0=T.val 0 1 :=
    (Matrix.isHermitian_iff_isSymm.mp T.property.1.isHermitian).apply 0 1
  rw [shapeMatrix_formula,shapeRoot_inv_sq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [binaryX,Matrix.det_fin_two,hs,smul_eq_mul] <;> field_simp [hb]
  ring

@[simp] theorem shapePoint_reconstruct (T : BinarySpace) :
    shapePoint (binaryX T.val) (shapeRoot T) (shapeRoot_pos T)=T := by
  apply Subtype.ext
  change binaryNormalize (shapeMatrix (binaryX T.val) (shapeRoot T))=T.val
  rw [shapeMatrix_reconstruct,binaryNormalize_smul _
    (inv_ne_zero (ne_of_gt T.property.1.diag_pos))]
  simp [binaryNormalize,T.property.2]

theorem shapeTrace_reconstruct (T : BinarySpace) :
    shapeTrace (binaryX T.val) (shapeRoot T)=(T.val 1 1)⁻¹ := by
  rw [←shapeMatrix_trace,shapeMatrix_reconstruct,trace_smul,T.property.2]
  simp

theorem continuous_shapeRoot : Continuous shapeRoot := by
  exact (continuous_subtype_val.matrix_elem 1 1).div₀
    continuous_subtype_val.matrix_det.sqrt
    (fun T => ne_of_gt (Real.sqrt_pos.mpr T.property.1.det_pos))

end TernaryPoly.SymmetricSpaceFlagPlaneHomeomorph
