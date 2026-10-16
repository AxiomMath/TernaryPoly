module

public import TernaryPeriodPolynomials.SymmetricSpace.Orientation.Matrix
public import Mathlib.LinearAlgebra.Matrix.Block

@[expose] public section

noncomputable section
namespace TernaryPoly.SymmetricSpaceOrientation
open Matrix

/-- Elementary upper transvection (0,1) is upper triangular on the actual six coordinates. -/
theorem coordinateMatrix_transvection01_upper (c : ℝ) :
    (coordinateMatrix (Matrix.transvection 0 1 c)).IsUpperTriangular := by
  intro i j h
  fin_cases i <;> fin_cases j <;>
    simp_all [coordinateMatrix,rowPair,Matrix.transvection,Matrix.single]

/-- Each diagonal coordinate of the (0,1) transvection action is exactly one. -/
theorem coordinateMatrix_transvection01_diag (c : ℝ) (i : Fin 6) :
    coordinateMatrix (Matrix.transvection 0 1 c) i i = 1 := by
  fin_cases i <;>
    simp [coordinateMatrix,rowPair,Matrix.transvection,Matrix.single]

theorem coordinateMatrix_transvection01_det (c : ℝ) :
    (coordinateMatrix (Matrix.transvection 0 1 c)).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular (coordinateMatrix_transvection01_upper c)]
  simp only [coordinateMatrix_transvection01_diag,Finset.prod_const_one]


/-- Elementary upper transvection (0,2) is upper triangular on the actual six coordinates. -/
theorem coordinateMatrix_transvection02_upper (c : ℝ) :
    (coordinateMatrix (Matrix.transvection 0 2 c)).IsUpperTriangular := by
  intro i j h
  fin_cases i <;> fin_cases j <;>
    simp_all [coordinateMatrix,rowPair,Matrix.transvection,Matrix.single]

/-- Each diagonal coordinate of the (0,2) transvection action is exactly one. -/
theorem coordinateMatrix_transvection02_diag (c : ℝ) (i : Fin 6) :
    coordinateMatrix (Matrix.transvection 0 2 c) i i = 1 := by
  fin_cases i <;>
    simp [coordinateMatrix,rowPair,Matrix.transvection,Matrix.single]

theorem coordinateMatrix_transvection02_det (c : ℝ) :
    (coordinateMatrix (Matrix.transvection 0 2 c)).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular (coordinateMatrix_transvection02_upper c)]
  simp only [coordinateMatrix_transvection02_diag,Finset.prod_const_one]


/-- Elementary lower transvection (1,0) is lower triangular on the actual six coordinates. -/
theorem coordinateMatrix_transvection10_lower (c : ℝ) :
    (coordinateMatrix (Matrix.transvection 1 0 c)).IsLowerTriangular := by
  intro i j h
  change i < j at h
  fin_cases i <;> fin_cases j <;>
    simp_all [coordinateMatrix,rowPair,Matrix.transvection,Matrix.single]

/-- Each diagonal coordinate of the (1,0) transvection action is exactly one. -/
theorem coordinateMatrix_transvection10_diag (c : ℝ) (i : Fin 6) :
    coordinateMatrix (Matrix.transvection 1 0 c) i i = 1 := by
  fin_cases i <;>
    simp [coordinateMatrix,rowPair,Matrix.transvection,Matrix.single]

theorem coordinateMatrix_transvection10_det (c : ℝ) :
    (coordinateMatrix (Matrix.transvection 1 0 c)).det = 1 := by
  rw [Matrix.det_of_isLowerTriangular _ (coordinateMatrix_transvection10_lower c)]
  simp only [coordinateMatrix_transvection10_diag,Finset.prod_const_one]


/-- Elementary upper transvection (1,2) is upper triangular on the actual six coordinates. -/
theorem coordinateMatrix_transvection12_upper (c : ℝ) :
    (coordinateMatrix (Matrix.transvection 1 2 c)).IsUpperTriangular := by
  intro i j h
  fin_cases i <;> fin_cases j <;>
    simp_all [coordinateMatrix,rowPair,Matrix.transvection,Matrix.single]

/-- Each diagonal coordinate of the (1,2) transvection action is exactly one. -/
theorem coordinateMatrix_transvection12_diag (c : ℝ) (i : Fin 6) :
    coordinateMatrix (Matrix.transvection 1 2 c) i i = 1 := by
  fin_cases i <;>
    simp [coordinateMatrix,rowPair,Matrix.transvection,Matrix.single]

theorem coordinateMatrix_transvection12_det (c : ℝ) :
    (coordinateMatrix (Matrix.transvection 1 2 c)).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular (coordinateMatrix_transvection12_upper c)]
  simp only [coordinateMatrix_transvection12_diag,Finset.prod_const_one]


/-- Elementary lower transvection (2,0) is lower triangular on the actual six coordinates. -/
theorem coordinateMatrix_transvection20_lower (c : ℝ) :
    (coordinateMatrix (Matrix.transvection 2 0 c)).IsLowerTriangular := by
  intro i j h
  change i < j at h
  fin_cases i <;> fin_cases j <;>
    simp_all [coordinateMatrix,rowPair,Matrix.transvection,Matrix.single]

/-- Each diagonal coordinate of the (2,0) transvection action is exactly one. -/
theorem coordinateMatrix_transvection20_diag (c : ℝ) (i : Fin 6) :
    coordinateMatrix (Matrix.transvection 2 0 c) i i = 1 := by
  fin_cases i <;>
    simp [coordinateMatrix,rowPair,Matrix.transvection,Matrix.single]

theorem coordinateMatrix_transvection20_det (c : ℝ) :
    (coordinateMatrix (Matrix.transvection 2 0 c)).det = 1 := by
  rw [Matrix.det_of_isLowerTriangular _ (coordinateMatrix_transvection20_lower c)]
  simp only [coordinateMatrix_transvection20_diag,Finset.prod_const_one]


/-- Elementary lower transvection (2,1) is lower triangular on the actual six coordinates. -/
theorem coordinateMatrix_transvection21_lower (c : ℝ) :
    (coordinateMatrix (Matrix.transvection 2 1 c)).IsLowerTriangular := by
  intro i j h
  change i < j at h
  fin_cases i <;> fin_cases j <;>
    simp_all [coordinateMatrix,rowPair,Matrix.transvection,Matrix.single]

/-- Each diagonal coordinate of the (2,1) transvection action is exactly one. -/
theorem coordinateMatrix_transvection21_diag (c : ℝ) (i : Fin 6) :
    coordinateMatrix (Matrix.transvection 2 1 c) i i = 1 := by
  fin_cases i <;>
    simp [coordinateMatrix,rowPair,Matrix.transvection,Matrix.single]

theorem coordinateMatrix_transvection21_det (c : ℝ) :
    (coordinateMatrix (Matrix.transvection 2 1 c)).det = 1 := by
  rw [Matrix.det_of_isLowerTriangular _ (coordinateMatrix_transvection21_lower c)]
  simp only [coordinateMatrix_transvection21_diag,Finset.prod_const_one]


/-- All elementary generators have determinant one in the actual symmetric-square action. -/
theorem coordinateMatrix_det_transvection (t : Matrix.TransvectionStruct (Fin 3) ℝ) :
    (coordinateMatrix t.toMatrix).det = 1 := by
  rcases t with ⟨i,j,hij,c⟩
  fin_cases i <;> fin_cases j
  · exact False.elim (hij rfl)
  · exact coordinateMatrix_transvection01_det c
  · exact coordinateMatrix_transvection02_det c
  · exact coordinateMatrix_transvection10_det c
  · exact False.elim (hij rfl)
  · exact coordinateMatrix_transvection12_det c
  · exact coordinateMatrix_transvection20_det c
  · exact coordinateMatrix_transvection21_det c
  · exact False.elim (hij rfl)

end TernaryPoly.SymmetricSpaceOrientation
