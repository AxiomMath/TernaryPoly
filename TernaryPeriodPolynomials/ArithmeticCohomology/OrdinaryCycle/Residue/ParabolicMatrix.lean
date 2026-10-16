module

public import TernaryPeriodPolynomials.SymmetricSolution.SinglePole.CoordinateResidue

@[expose] public section


open Matrix MvPolynomial
noncomputable section
namespace TernaryPoly.OrdinaryResidueParabolic
open PolynomialGLAction SinglePoleCoordinate

abbrev GL2 := Matrix.GeneralLinearGroup (Fin 2) ℚ
abbrev Mat3 := Matrix (Fin 3) (Fin 3) ℚ

/-- Literal lower block-parabolic matrix in the ordered coordinates (a,b,c). -/
def blockMatrix (lam : ℚˣ) (u : Fin 2 → ℚ) (C : GL2) : Mat3 :=
  ![![(lam : ℚ),0,0],![u 0,C.val 0 0,C.val 0 1],![u 1,C.val 1 0,C.val 1 1]]

def lowerBlock (M : Mat3) : Matrix (Fin 2) (Fin 2) ℚ := fun i j => M i.succ j.succ

/-- Inverting the actual block matrix scales a by lambda inverse and introduces no b or c in a. -/
theorem inverse_first_row (g : GL3) (lam : ℚˣ) (u : Fin 2 → ℚ) (C : GL2)
    (hg : g.val = blockMatrix lam u C) (j : Fin 3) :
    (g⁻¹).val 0 j = (![ (lam : ℚ)⁻¹,0,0] : Fin 3 → ℚ) j := by
  have h : (lam : ℚ) * (g⁻¹).val 0 j = (1 : Mat3) 0 j := by
    have he := congrArg (fun M : Mat3 => M 0 j) g.val_inv
    change (g.val * (g⁻¹).val) 0 j = (1 : Mat3) 0 j at he
    rw [Matrix.mul_apply,Fin.sum_univ_three] at he
    simpa [hg,blockMatrix] using he
  apply mul_left_cancel₀ (Units.ne_zero lam)
  fin_cases j <;> simpa [Matrix.one_apply,Units.ne_zero lam] using h

/-- The lower-right block of the inverse is C inverse, irrespective of the lower-left shear. -/
theorem inverse_lowerBlock (g : GL3) (lam : ℚˣ) (u : Fin 2 → ℚ) (C : GL2)
    (hg : g.val = blockMatrix lam u C) : lowerBlock (g⁻¹).val = (C⁻¹).val := by
  have h : lowerBlock (g⁻¹).val * C.val = 1 := by
    ext i j
    have he := congrArg (fun M : Mat3 => M i.succ j.succ) g.inv_val
    change ((g⁻¹).val * g.val) i.succ j.succ = (1 : Mat3) i.succ j.succ at he
    rw [Matrix.mul_apply,Fin.sum_univ_three] at he
    fin_cases i <;> fin_cases j <;>
      simpa [lowerBlock,Matrix.mul_apply,Fin.sum_univ_two,Fin.sum_univ_three,hg,blockMatrix] using he
  calc
    lowerBlock (g⁻¹).val = lowerBlock (g⁻¹).val * (C.val * (C⁻¹).val) := by
      have hi : C.val * (C⁻¹).val = 1 := C.val_inv
      rw [hi,mul_one]
    _ = (C⁻¹).val := by rw [←mul_assoc,h,one_mul]

/-- The actual determinant contains no contribution from the lower-left shear. -/
theorem determinant_block (g : GL3) (lam : ℚˣ) (u : Fin 2 → ℚ) (C : GL2)
    (hg : g.val = blockMatrix lam u C) : g.val.det = (lam : ℚ) * C.val.det := by
  rw [hg,Matrix.det_fin_three,Matrix.det_fin_two]
  simp only [blockMatrix,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.head_cons,Matrix.tail_cons,zero_mul,add_zero,sub_zero]
  ring

/-- The determinant twist and inverse normal scaling cancel lambda exactly. -/
theorem determinant_residue_scalar (g : GL3) (lam : ℚˣ) (u : Fin 2 → ℚ) (C : GL2)
    (hg : g.val = blockMatrix lam u C) :
    determinantCharacter (-1) g * (lam : ℚ) = (C.val.det)⁻¹ := by
  change g.val.det ^ (-1 : ℤ) * (lam : ℚ) = _
  rw [determinant_block g lam u C hg,zpow_neg_one,_root_.mul_inv_rev]
  rw [mul_assoc,inv_mul_cancel₀ (Units.ne_zero lam),mul_one]

end TernaryPoly.OrdinaryResidueParabolic
