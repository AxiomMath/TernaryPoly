module

public import TernaryPeriodPolynomials.SymmetricSpace.Parabolic.CoordinatesBasic

@[expose] public section


open Matrix
noncomputable section
namespace TernaryPoly.SymmetricSpaceParabolicCoordinates
open SymmetricSpacePositive

abbrev RealGL2 := GeneralLinearGroup (Fin 2) ℝ

/-- The actual real plane-parabolic block matrix, retaining the sign of d. -/
def blockMatrix (A : Mat2) (u : Vec2) (d : ℝ) : Mat :=
  !![A 0 0,A 0 1,u 0;A 1 0,A 1 1,u 1;0,0,d]

theorem blockMatrix_det (A : Mat2) (u : Vec2) (d : ℝ) :
    (blockMatrix A u d).det=A.det*d := by
  simp [blockMatrix,Matrix.det_fin_three,Matrix.det_fin_two]
  ring

/-- Every invertible binary block and every nonzero real d give a genuine GL3 element. -/
def parabolicGL (A : RealGL2) (u : Vec2) (d : ℝ) (hd : d≠0) : RealGL :=
  GeneralLinearGroup.mkOfDetNeZero (blockMatrix A.val u d)
    (by rw [blockMatrix_det]; exact mul_ne_zero A.det_ne_zero hd)

@[simp] theorem parabolicGL_val (A : RealGL2) (u : Vec2) (d : ℝ) (hd : d≠0) :
    (parabolicGL A u d hd).val=blockMatrix A.val u d := rfl

def transformedUnipotent (A : Mat2) (u : Vec2) (d : ℝ) (v : Vec2) : Vec2 :=
  d⁻¹ • (A *ᵥ v+u)

def transformedSchur (A : Mat2) (d : ℝ) (B : Mat2) : Mat2 :=
  (d⁻¹)^2 • (A*B*star A)

/-- Exact block congruence algebra, before any trace normalization or positivity assumption. -/
theorem blockMatrix_assemble (A : Mat2) (u : Vec2) (d : ℝ) (hd : d≠0)
    (v : Vec2) (B : Mat2) :
    blockMatrix A u d*assemble v B*star (blockMatrix A u d)=
      d^2 • assemble (transformedUnipotent A u d v) (transformedSchur A d B) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockMatrix,assemble,transformedUnipotent,transformedSchur,Matrix.mul_apply,
      Matrix.mulVec,dotProduct,Matrix.star_apply,Fin.sum_univ_succ,smul_eq_mul] <;>
    field_simp [hd] <;> ring

end TernaryPoly.SymmetricSpaceParabolicCoordinates
