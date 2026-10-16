module

public import TernaryPeriodPolynomials.SymmetricSpace.PositiveAction
public import Mathlib.Tactic
public import Mathlib.Algebra.Order.Interval.Set.Group
public import Mathlib.Algebra.Order.Monoid.Submonoid
public import Mathlib.Algebra.Order.Ring.Interval
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.Data.Nat.NthRoot.Defs
public import Mathlib.GroupTheory.QuotientGroup.ModEq
public import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
public import Mathlib.NumberTheory.MulChar.Lemmas
public import Mathlib.RingTheory.FreeCommRing
public import Mathlib.RingTheory.SimpleRing.Matrix
public import Mathlib.RingTheory.Valuation.IsTrivialOn
public import Mathlib.Topology.Algebra.Module.UniformConvergence
public import Mathlib.Topology.Algebra.SeparationQuotient.Section
public import Mathlib.Topology.Order.AtTopBotIxx

@[expose] public section


open Matrix
noncomputable section
namespace TernaryPoly.SymmetricSpaceParabolicCoordinates
open SymmetricSpacePositive

abbrev Vec2 := Fin 2 → ℝ
abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℝ
abbrev PosDef2 := {B : Mat2 // B.PosDef}

/-- The literal inclusion of the first two coordinates into the three-coordinate matrix model. -/
def topIndex : Fin 2 → Fin 3 := Fin.castSucc

theorem topIndex_injective : Function.Injective topIndex := Fin.castSucc_injective 2

def height (S : Mat) : ℝ := S 2 2

def unipotent (S : Mat) : Vec2 := fun i => S (topIndex i) 2/height S

/-- The normalized positive Schur complement in the plane coordinates. -/
def schur (S : Mat) : Mat2 := fun i j =>
  S (topIndex i) (topIndex j)/height S-unipotent S i*unipotent S j

/-- The actual binary block plus the normalized one-dimensional complementary form. -/
def diagonalBlock (B : Mat2) : Mat :=
  !![B 0 0,B 0 1,0;B 1 0,B 1 1,0;0,0,1]

/-- The actual upper unipotent matrix with plane parameter v. -/
def shearMatrix (v : Vec2) : Mat := !![1,0,v 0;0,1,v 1;0,0,1]

/-- The inverse horospherical matrix before trace normalization. -/
def assemble (v : Vec2) (B : Mat2) : Mat :=
  !![B 0 0+v 0*v 0,B 0 1+v 0*v 1,v 0;
    B 1 0+v 1*v 0,B 1 1+v 1*v 1,v 1;v 0,v 1,1]

@[simp] theorem shearMatrix_det (v : Vec2) : (shearMatrix v).det=1 := by
  simp [shearMatrix,Matrix.det_fin_three]

def shearGL (v : Vec2) : RealGL :=
  GeneralLinearGroup.mkOfDetNeZero (shearMatrix v) (by rw [shearMatrix_det]; exact one_ne_zero)

@[simp] theorem shearGL_val (v : Vec2) : (shearGL v).val=shearMatrix v := rfl

theorem shear_diagonalBlock (v : Vec2) (B : Mat2) :
    shearMatrix v*diagonalBlock B*star (shearMatrix v)=assemble v B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [shearMatrix,diagonalBlock,assemble,Matrix.mul_apply,Matrix.star_apply,
      Fin.sum_univ_succ]

theorem unshear_assemble (v : Vec2) (B : Mat2) :
    shearMatrix (-v)*assemble v B*star (shearMatrix (-v))=diagonalBlock B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [shearMatrix,diagonalBlock,assemble,Matrix.mul_apply,Matrix.star_apply,
      Fin.sum_univ_succ]

@[simp] theorem diagonalBlock_top (B : Mat2) :
    (diagonalBlock B).submatrix topIndex topIndex=B := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

@[simp] theorem height_assemble (v : Vec2) (B : Mat2) : height (assemble v B)=1 := rfl

@[simp] theorem unipotent_assemble (v : Vec2) (B : Mat2) : unipotent (assemble v B)=v := by
  ext i
  fin_cases i <;> simp [unipotent,height,assemble,topIndex]

@[simp] theorem schur_assemble (v : Vec2) (B : Mat2) : schur (assemble v B)=B := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [schur,unipotent,height,assemble,topIndex]

/-- The Schur coordinates recover the original symmetric matrix up to its positive last entry. -/
theorem assemble_coordinates (S : Mat) (hS : S.IsSymm) (ha : height S≠0) :
    assemble (unipotent S) (schur S)=(height S)⁻¹ • S := by
  have h02 := hS.apply 0 2
  have h12 := hS.apply 1 2
  change S 2 2≠0 at ha
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [assemble,schur,unipotent,height,topIndex,Matrix.smul_apply,smul_eq_mul,
      h02,h12,div_eq_mul_inv,ha] <;> ring

/-- These are projective coordinates: every nonzero real scalar leaves v unchanged. -/
theorem unipotent_smul (r : ℝ) (hr : r≠0) (S : Mat) :
    unipotent (r • S)=unipotent S := by
  ext i
  change r*S (topIndex i) 2/(r*height S)=S (topIndex i) 2/height S
  exact mul_div_mul_left _ _ hr

/-- The normalized Schur complement is also invariant under every nonzero scalar. -/
theorem schur_smul (r : ℝ) (hr : r≠0) (S : Mat) : schur (r • S)=schur S := by
  ext i j
  change r*S (topIndex i) (topIndex j)/(r*height S)-
    unipotent (r • S) i*unipotent (r • S) j=
    S (topIndex i) (topIndex j)/height S-unipotent S i*unipotent S j
  rw [unipotent_smul r hr,mul_div_mul_left _ _ hr]

end TernaryPoly.SymmetricSpaceParabolicCoordinates
