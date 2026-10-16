module

public import TernaryPeriodPolynomials.SymmetricSpace.Flag.CoordinatesRoots
public import TernaryPeriodPolynomials.SymmetricSpace.Parabolic.Coordinates

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceFlagCoordinates
open Matrix
open SymmetricSpacePositive SymmetricSpaceParabolicCoordinates

/-- The binary shape matrix in the flag-to-plane overlap. -/
def shapeMatrix (x t1 : ℝ) : Mat2 := binaryLDL x (t1^2)⁻¹ 1

/-- Its actual trace is the overlap's positive radial denominator squared. -/
def shapeTrace (x t1 : ℝ) : ℝ := x^2+(t1^2)⁻¹+1

@[simp] theorem shapeMatrix_formula (x t1 : ℝ) :
    shapeMatrix x t1=!![x^2+(t1^2)⁻¹,x;x,1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [shapeMatrix,binaryLDL,add_comm]

@[simp] theorem shapeMatrix_trace (x t1 : ℝ) : (shapeMatrix x t1).trace=shapeTrace x t1 := by
  simp [shapeMatrix_formula,shapeTrace,Matrix.trace,Fin.sum_univ_succ]

theorem shapeMatrix_positive (x t1 : ℝ) (ht : 0<t1) : (shapeMatrix x t1).PosDef :=
  binaryLDL_positive x _ 1 (inv_pos.mpr (pow_pos ht 2)) zero_lt_one

theorem shapeTrace_pos (x t1 : ℝ) : 0<shapeTrace x t1 := by
  dsimp [shapeTrace]
  positivity

/-- The actual plane unipotent coordinate is exactly (z,y). -/
theorem root_unipotent (p : RootParameters) :
    unipotent (rootHomeomorph.symm p).val=![p.1 2,p.1 1] := by
  rw [rootHomeomorph_symm,flagMatrix_eq_assemble]
  apply unipotent_normalize_assemble
  exact binaryLDL_positive _ _ _
    (inv_pos.mpr (mul_pos (pow_pos p.2.1.property 2) (pow_pos p.2.2.property 2)))
    (inv_pos.mpr (pow_pos p.2.2.property 2))

/-- The actual plane Schur matrix in simple-root coordinates, before removing its scale. -/
theorem root_schur (p : RootParameters) :
    schur (rootHomeomorph.symm p).val=
      binaryLDL (p.1 0) (p.2.1.val^2*p.2.2.val^2)⁻¹ (p.2.2.val^2)⁻¹ := by
  rw [rootHomeomorph_symm,flagMatrix_eq_assemble]
  apply schur_normalize_assemble
  exact binaryLDL_positive _ _ _
    (inv_pos.mpr (mul_pos (pow_pos p.2.1.property 2) (pow_pos p.2.2.property 2)))
    (inv_pos.mpr (pow_pos p.2.2.property 2))

theorem root_schur_factor (p : RootParameters) :
    schur (rootHomeomorph.symm p).val=
      (p.2.2.val^2)⁻¹ • shapeMatrix (p.1 0) p.2.1.val := by
  rw [root_schur]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [binaryLDL,shapeMatrix,Matrix.smul_apply,smul_eq_mul,_root_.mul_inv_rev]
  all_goals ring

theorem root_schur_trace (p : RootParameters) :
    (schur (rootHomeomorph.symm p).val).trace=
      (p.2.2.val^2)⁻¹*shapeTrace (p.1 0) p.2.1.val := by
  rw [root_schur_factor,trace_smul,shapeMatrix_trace,smul_eq_mul]

/-- Removing the binary trace scale gives the exact overlap shape. -/
theorem root_plane_shape (p : RootParameters) :
    binaryNormalize (schur (rootHomeomorph.symm p).val)=
      binaryNormalize (shapeMatrix (p.1 0) p.2.1.val) := by
  rw [root_schur_factor,binaryNormalize_smul _
    (inv_ne_zero (pow_ne_zero 2 (ne_of_gt p.2.2.property)))]

/-- The actual reciprocal-square-root plane parameter has the claimed flag-overlap formula. -/
theorem root_plane_parameter (p : RootParameters) :
    (Real.sqrt (schur (rootHomeomorph.symm p).val).trace)⁻¹=
      p.2.2.val/Real.sqrt (shapeTrace (p.1 0) p.2.1.val) := by
  rw [root_schur_trace,Real.sqrt_mul (inv_nonneg.mpr (sq_nonneg _)),Real.sqrt_inv,
    Real.sqrt_sq p.2.2.property.le,_root_.mul_inv_rev,inv_inv,div_eq_mul_inv]
  ring

end TernaryPoly.SymmetricSpaceFlagCoordinates
