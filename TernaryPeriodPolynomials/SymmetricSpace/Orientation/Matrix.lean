module

public import TernaryPeriodPolynomials.SymmetricSpace.Orientation
public import Mathlib.LinearAlgebra.Matrix.Transvection

@[expose] public section

noncomputable section
namespace TernaryPoly.SymmetricSpaceOrientation
open Matrix

abbrev Mat6 := Matrix (Fin 6) (Fin 6) ℝ

/-- The three diagonal pairs and three off-diagonal pairs, in lexicographic order. -/
def rowPair : Fin 6 → Fin 3 × Fin 3 := ![(0,0),(0,1),(0,2),(1,1),(1,2),(2,2)]

/-- Explicit coefficients of S↦g*S*gᵀ on (S00,S01,S02,S11,S12,S22). -/
def coordinateMatrix (g : Mat3) : Mat6 := fun k =>
  let i := (rowPair k).1
  let j := (rowPair k).2
  ![g i 0*g j 0,
    g i 0*g j 1+g i 1*g j 0,
    g i 0*g j 2+g i 2*g j 0,
    g i 1*g j 1,
    g i 1*g j 2+g i 2*g j 1,
    g i 2*g j 2]

/-- The explicit quadratic matrix really represents the actual congruence action. -/
theorem coordinateMatrix_eq_toMatrix (g : Mat3) :
    coordinateMatrix g = LinearMap.toMatrix' (coordinateAction g) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coordinateMatrix,rowPair,LinearMap.toMatrix'_apply,coordinateAction,
      coordinates,fromCoordinates,congruence,Matrix.mul_apply,Fin.sum_univ_three,
      Matrix.transpose_apply] <;> ring

@[simp] theorem coordinateMatrix_one : coordinateMatrix (1 : Mat3) = 1 := by
  rw [coordinateMatrix_eq_toMatrix,coordinateAction_one,LinearMap.toMatrix'_id]

/-- Multiplicativity follows from the actual action, not a stipulated character. -/
theorem coordinateMatrix_mul (g h : Mat3) :
    coordinateMatrix (g*h) = coordinateMatrix g*coordinateMatrix h := by
  rw [coordinateMatrix_eq_toMatrix,coordinateAction_mul,LinearMap.toMatrix'_comp,
    ←coordinateMatrix_eq_toMatrix,←coordinateMatrix_eq_toMatrix]

/-- A diagonal matrix acts on the six literal coordinates by these six monomials. -/
theorem coordinateMatrix_diagonal (d : Fin 3 → ℝ) :
    coordinateMatrix (Matrix.diagonal d) =
      Matrix.diagonal ![d 0^2,d 0*d 1,d 0*d 2,d 1^2,d 1*d 2,d 2^2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coordinateMatrix,rowPair,pow_two]

/-- The determinant formula for the diagonal generators. -/
theorem coordinateMatrix_det_diagonal (d : Fin 3 → ℝ) :
    (coordinateMatrix (Matrix.diagonal d)).det = (Matrix.diagonal d).det^4 := by
  rw [coordinateMatrix_diagonal,Matrix.det_diagonal,Matrix.det_diagonal]
  simp only [Fin.prod_univ_succ,Fin.prod_univ_zero,Fin.succ_zero_eq_one,Fin.succ_one_eq_two,
    Matrix.cons_val_zero,Matrix.cons_val_succ,mul_one]
  ring

end TernaryPoly.SymmetricSpaceOrientation
