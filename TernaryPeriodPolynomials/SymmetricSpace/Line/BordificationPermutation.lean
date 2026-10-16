module

public import TernaryPeriodPolynomials.SymmetricSpace.Line.BordificationDuality
public import Mathlib.Tactic.FinCases

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceLineBordification
open Matrix
open SymmetricSpacePositive

def flipMatrix : Mat := !![0,0,1;0,1,0;1,0,0]

@[simp] theorem flipMatrix_mul_self : flipMatrix*flipMatrix=1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [flipMatrix,Matrix.mul_apply,Fin.sum_univ_succ]

@[simp] theorem flipMatrix_star : star flipMatrix=flipMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- The explicit orthogonal swap of e0 and e2, retaining e1. -/
def flipGL : RealGL := ⟨flipMatrix,flipMatrix,flipMatrix_mul_self,flipMatrix_mul_self⟩

@[simp] theorem flipGL_inv : flipGL⁻¹=flipGL := rfl
@[simp] theorem flipGL_star : star flipGL=flipGL := Units.ext flipMatrix_star
@[simp] theorem flipGL_mul_self : flipGL*flipGL=1 := Units.ext flipMatrix_mul_self
@[simp] theorem flipGL_cancel (g : RealGL) : flipGL*(flipGL*g)=g := by
  rw [←mul_assoc,flipGL_mul_self,one_mul]

@[simp] theorem contragredient_flip : contragredient flipGL=flipGL := by simp [contragredient]

/-- The involution taking the e0-line stabilizer to the e0,e1-plane stabilizer. -/
def dualGL (g : RealGL) : RealGL := flipGL*contragredient g*flipGL

theorem dualGL_mul (g h : RealGL) : dualGL (g*h)=dualGL g*dualGL h := by
  simp [dualGL,contragredient_mul,mul_assoc]

@[simp] theorem dualGL_involutive (g : RealGL) : dualGL (dualGL g)=g := by
  simp [dualGL,contragredient_mul,mul_assoc]

def dualGLEquiv : RealGL ≃* RealGL where
  toFun := dualGL
  invFun := dualGL
  left_inv := dualGL_involutive
  right_inv := dualGL_involutive
  map_mul' := dualGL_mul

/-- Normalized inverse-form duality, followed by the explicit e0/e2 swap. -/
def dualForm (S : Space) : Space := act flipGL (inverseForm S)

@[simp] theorem dualForm_involutive (S : Space) : dualForm (dualForm S)=S := by
  simp only [dualForm,inverseForm_act,contragredient_flip,inverseForm_involutive]
  rw [←act_mul,flipGL_mul_self,act_one]

def dualFormHomeomorph : Space ≃ₜ Space where
  toFun := dualForm
  invFun := dualForm
  left_inv := dualForm_involutive
  right_inv := dualForm_involutive
  continuous_toFun := (continuous_act flipGL).comp continuous_inverseForm
  continuous_invFun := (continuous_act flipGL).comp continuous_inverseForm

theorem dualForm_act (g : RealGL) (S : Space) :
    dualForm (act g S)=act (dualGL g) (dualForm S) := by
  simp only [dualForm,inverseForm_act,dualGL]
  simp only [←act_mul,mul_assoc,flipGL_mul_self,mul_one]

theorem continuous_dualGL : Continuous dualGL := by
  apply Units.continuous_iff.mpr
  constructor
  · exact ((continuous_const : Continuous (fun _ : RealGL => flipMatrix)).mul
      Units.continuous_coe_inv.star).mul continuous_const
  · have h : Continuous (fun g : RealGL => flipMatrix*star g.val*flipMatrix) :=
      ((continuous_const : Continuous (fun _ : RealGL => flipMatrix)).mul
        Units.continuous_val.star).mul continuous_const
    simpa [dualGL,contragredient,mul_assoc,flipGL] using h

end TernaryPoly.SymmetricSpaceLineBordification
