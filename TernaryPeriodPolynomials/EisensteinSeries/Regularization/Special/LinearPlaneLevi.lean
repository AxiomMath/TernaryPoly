module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Real.PlaneSlice
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Plane.LeviMultiplication

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

def specialLinearPlaneLevi {R : Type*} [CommRing R] :
    SpecialLinearGroup (Fin 2) R →* SpecialLinearGroup (Fin 3) R where
  toFun matrix := ⟨planeBlock matrix.val 1, by
    have determinant := matrix.property
    simp only [Matrix.det_fin_two] at determinant
    simpa [planeBlock, Matrix.det_fin_three] using determinant⟩
  map_one' := by
    apply Subtype.ext
    ext row column
    fin_cases row <;> fin_cases column <;> simp [planeBlock]
  map_mul' first second := by
    apply Subtype.ext
    ext row column
    fin_cases row <;> fin_cases column <;>
      simp [planeBlock, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two]

theorem specialLinearPlaneLevi_injective {R : Type*} [CommRing R] :
    Function.Injective (specialLinearPlaneLevi (R := R)) := by
  intro first second equal
  apply Subtype.ext
  ext row column
  have entry := congrArg (fun matrix : SpecialLinearGroup (Fin 3) R =>
    matrix.val row.castSucc column.castSucc) equal
  fin_cases row <;> fin_cases column <;>
    simpa [specialLinearPlaneLevi, planeBlock] using entry

theorem specialLinearPlaneLevi_mul_last_row {R : Type*} [CommRing R]
    (binary : SpecialLinearGroup (Fin 2) R) (matrix : SpecialLinearGroup (Fin 3) R) (column : Fin 3) :
    (specialLinearPlaneLevi binary * matrix).val 2 column = matrix.val 2 column := by
  simp [specialLinearPlaneLevi, planeBlock, Matrix.mul_apply, Fin.sum_univ_three]

theorem specialLinearPlaneLevi_mul_first_rows {R : Type*} [CommRing R]
    (binary : SpecialLinearGroup (Fin 2) R) (matrix : SpecialLinearGroup (Fin 3) R)
    (row : Fin 2) (column : Fin 3) :
    (specialLinearPlaneLevi binary * matrix).val row.castSucc column =
      ∑ inner : Fin 2, binary.val row inner * matrix.val inner.castSucc column := by
  fin_cases row <;>
    simp [specialLinearPlaneLevi, planeBlock, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two]

theorem realPlaneRowSquare_levi_mul (binary : SpecialLinearGroup (Fin 2) ℝ)
    (matrix : SpecialLinearGroup (Fin 3) ℝ) :
    realPlaneRowSquare (specialLinearPlaneLevi binary * matrix) = realPlaneRowSquare matrix := by
  simp only [realPlaneRowSquare, specialLinearPlaneLevi_mul_last_row]

theorem realPlaneCoordinate_levi_mul (binary : SpecialLinearGroup (Fin 2) ℝ)
    (matrix : SpecialLinearGroup (Fin 3) ℝ) (row : Fin 2) :
    realPlaneCoordinate (specialLinearPlaneLevi binary * matrix) row =
      ∑ inner : Fin 2, binary.val row inner * realPlaneCoordinate matrix inner := by
  simp only [realPlaneCoordinate, realPlaneRowSquare_levi_mul,
    specialLinearPlaneLevi_mul_first_rows, specialLinearPlaneLevi_mul_last_row,
    Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]
  simp only [Finset.sum_div, ← Finset.mul_sum, mul_div_assoc]

theorem realPlaneNormalSet_levi_invariant (binary : SpecialLinearGroup (Fin 2) ℝ)
    (matrix : SpecialLinearGroup (Fin 3) ℝ) (member : matrix ∈ realPlaneNormalSet) :
    specialLinearPlaneLevi binary * matrix ∈ realPlaneNormalSet := by
  change ∀ row, realPlaneCoordinate matrix row = 0 at member
  change ∀ row, realPlaneCoordinate (specialLinearPlaneLevi binary * matrix) row = 0
  intro row
  rw [realPlaneCoordinate_levi_mul]
  simp only [member, mul_zero, Finset.sum_const_zero]

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
