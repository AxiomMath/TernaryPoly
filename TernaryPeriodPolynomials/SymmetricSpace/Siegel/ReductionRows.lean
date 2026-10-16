module

public import TernaryPeriodPolynomials.SymmetricSpace.Siegel.ReductionFinite
public import Mathlib.LinearAlgebra.Matrix.Transvection

@[expose] public section

noncomputable section
namespace TernaryPoly.SymmetricSpaceSiegelReduction
open Matrix SymmetricSpacePositive SymmetricSpaceArithmeticProper

def row (g : IntegralGL) (i : Fin 3) : IntVector := g.val i

/-- A literal integer elementary row shear with its actual inverse. -/
def shear (i j : Fin 3) (h : i≠j) (n : ℤ) : IntegralGL where
  val := Matrix.transvection i j n
  inv := Matrix.transvection i j (-n)
  val_inv := by rw [Matrix.transvection_mul_transvection_same i j h,add_neg_cancel,Matrix.transvection_zero]
  inv_val := by rw [Matrix.transvection_mul_transvection_same i j h,neg_add_cancel,Matrix.transvection_zero]

theorem row_shear_same (g : IntegralGL) (i j : Fin 3) (h : i≠j) (n : ℤ) :
    row (shear i j h n*g) i=row g i+n • row g j := by
  ext k
  exact Matrix.transvection_mul_apply_same i j k n g.val

theorem row_shear_ne (g : IntegralGL) (i j k : Fin 3) (h : i≠j) (hk : k≠i) (n : ℤ) :
    row (shear i j h n*g) k=row g k := by
  ext l
  exact Matrix.transvection_mul_apply_of_ne i j k l hk n g.val

/-- The permutation exchanging the two lower rows is an actual integral unit. -/
def swap12 : IntegralGL where
  val := !![1,0,0;0,0,1;0,1,0]
  inv := !![1,0,0;0,0,1;0,1,0]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply,Fin.sum_univ_succ]
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply,Fin.sum_univ_succ]

/-- The permutation exchanging the two upper rows fixes the last row. -/
def swap01 : IntegralGL where
  val := !![0,1,0;1,0,0;0,0,1]
  inv := !![0,1,0;1,0,0;0,0,1]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply,Fin.sum_univ_succ]
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply,Fin.sum_univ_succ]

@[simp] theorem row_swap12_one (g : IntegralGL) : row (swap12*g) 1=row g 2 := by
  ext j
  simp [row,swap12,Matrix.mul_apply,Fin.sum_univ_succ]

@[simp] theorem row_swap12_two (g : IntegralGL) : row (swap12*g) 2=row g 1 := by
  ext j
  simp [row,swap12,Matrix.mul_apply,Fin.sum_univ_succ]

@[simp] theorem row_swap01_one (g : IntegralGL) : row (swap01*g) 1=row g 0 := by
  ext j
  simp [row,swap01,Matrix.mul_apply,Fin.sum_univ_succ]

@[simp] theorem row_swap01_two (g : IntegralGL) : row (swap01*g) 2=row g 2 := by
  ext j
  simp [row,swap01,Matrix.mul_apply,Fin.sum_univ_succ]

@[simp] theorem realVector_add_smul (v w : IntVector) (n : ℤ) :
    realVector (v+n • w)=realVector v+(n : ℝ) • realVector w := by
  ext i
  simp [realVector,smul_eq_mul]

theorem energy_row_pos (S : Space) (g : IntegralGL) (i : Fin 3) : 0<energy S (row g i) := by
  change 0<quadratic S.val ((realIntegral g).val i)
  rw [row_quadratic]
  exact (conjugate_positive (realIntegral g) S.val S.property.1).diag_pos

/-- A shortest admissible last row exists without assuming primitive-vector completion. -/
theorem exists_minimal_last_row (S : Space) :
    ∃ g : IntegralGL, ∀ h : IntegralGL, energy S (row g 2)≤energy S (row h 2) := by
  obtain ⟨v,⟨g,rfl⟩,hmin⟩ := exists_min_energy S (Set.range (fun g : IntegralGL => row g 2))
    ⟨row 1 2,⟨1,rfl⟩⟩
  exact ⟨g,fun h => hmin (row h 2) ⟨h,rfl⟩⟩

end TernaryPoly.SymmetricSpaceSiegelReduction
