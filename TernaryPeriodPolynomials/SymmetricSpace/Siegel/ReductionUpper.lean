module

public import TernaryPeriodPolynomials.SymmetricSpace.Siegel.ReductionRows
public import TernaryPeriodPolynomials.SymmetricSpace.Flag.Coordinates

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceSiegelReduction
open Matrix SymmetricSpacePositive SymmetricSpaceArithmeticProper SymmetricSpaceFlagCoordinates

/-- Every integer upper-unitriangular matrix is an actual unit over the integers. -/
def upperIntegral (m n k : ℤ) : IntegralGL where
  val := !![1,m,k;0,1,n;0,0,1]
  inv := !![1,-m,m*n-k;0,1,-n;0,0,1]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply,Fin.sum_univ_succ]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply,Fin.sum_univ_succ]
    ring

@[simp] theorem row_upper_two (m n k : ℤ) (g : IntegralGL) :
    row (upperIntegral m n k*g) 2=row g 2 := by
  ext j
  simp [row,upperIntegral,Matrix.mul_apply,Fin.sum_univ_succ]

@[simp] theorem row_upper_one (m n k : ℤ) (g : IntegralGL) :
    row (upperIntegral m n k*g) 1=row g 1+n • row g 2 := by
  ext j
  simp [row,upperIntegral,Matrix.mul_apply,Fin.sum_univ_succ]

@[simp] theorem realIntegral_upper (m n k : ℤ) :
    (realIntegral (upperIntegral m n k)).val=upper (m : ℝ) (n : ℝ) (k : ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [realIntegral_apply,upperIntegral,upper]

theorem upper_mul (m n k x y z : ℝ) :
    upper m n k*upper x y z=upper (x+m) (y+n) (z+m*y+k) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upper,Matrix.mul_apply,Fin.sum_univ_succ]
  ring

theorem conjugate_flag_upper (m n k : ℤ) (x y z a b : ℝ) :
    conjugate (realIntegral (upperIntegral m n k)) (flagMatrix x y z a b)=
      flagMatrix (x+m) (y+n) (z+m*y+k) a b := by
  simp only [conjugate,realIntegral_upper,Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial,flagMatrix]
  calc
    _=(upper (m : ℝ) n k*upper x y z)*diagonal a b*
        (upper (m : ℝ) n k*upper x y z).transpose := by
      simp only [Matrix.transpose_mul,mul_assoc]
    _=_ := by rw [upper_mul]

/-- The exact transformed LDL tuple retains both positive pivots. -/
def upperCoordinates (m n k : ℤ) (p : LDLParameters) : LDLParameters :=
  (![p.1 0+m,p.1 1+n,p.1 2+m*p.1 1+k],p.2)

theorem act_upper_inverse_coordinates (m n k : ℤ) (p : LDLParameters) :
    act (realIntegral (upperIntegral m n k)) (ldlHomeomorph.symm p)=
      ldlHomeomorph.symm (upperCoordinates m n k p) := by
  apply Subtype.ext
  change normalize (conjugate (realIntegral (upperIntegral m n k)) (ldlHomeomorph.symm p).val)=_
  rw [ldlHomeomorph_symm,ldlHomeomorph_symm]
  change normalize (conjugate (realIntegral (upperIntegral m n k))
    ((flagMatrix (p.1 0) (p.1 1) (p.1 2) p.2.1.val p.2.2.val).trace⁻¹ •
      flagMatrix (p.1 0) (p.1 1) (p.1 2) p.2.1.val p.2.2.val))=_
  rw [conjugate_smul,normalize_smul _ (inv_ne_zero (ne_of_gt
    (flagMatrix_positive _ _ _ _ _ p.2.1.property p.2.2.property).trace_pos)),
    conjugate_flag_upper]
  rfl

/-- Integer upper row operations act by the exact polynomial changes of the unipotent coordinates. -/
theorem ldlHomeomorph_act_upper (m n k : ℤ) (S : Space) :
    ldlHomeomorph (act (realIntegral (upperIntegral m n k)) S)=
      upperCoordinates m n k (ldlHomeomorph S) := by
  apply ldlHomeomorph.symm.injective
  rw [ldlHomeomorph.symm_apply_apply]
  have h := act_upper_inverse_coordinates m n k (ldlHomeomorph S)
  simpa only [ldlHomeomorph.symm_apply_apply] using h

end TernaryPoly.SymmetricSpaceSiegelReduction
