module

public import TernaryPeriodPolynomials.Building.BoundaryApartments.Apartment.FaceSubdivision
public import TernaryPeriodPolynomials.Building.BoundaryApartments.Apartment.Scaling

@[expose] public section


open GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers

open Matrix

/-- A singular frame contributes the zero apartment chain. -/
def matrixApartment (matrix : Matrix (Fin 3) (Fin 3) ℚ) : EdgeChains :=
  if nonzero : matrix.det ≠ 0 then
    apartment (GeneralLinearGroup.mkOfDetNeZero matrix nonzero)
  else 0

theorem rationalFrame_det_nonzero (frame : RationalGL3) : frame.val.det ≠ 0 :=
  ((Matrix.isUnit_iff_isUnit_det frame.val).mp frame.isUnit).ne_zero

theorem matrixApartment_frame (frame : RationalGL3) :
    matrixApartment frame.val = apartment frame := by
  rw [matrixApartment, dite_eq_left (rationalFrame_det_nonzero frame)]
  congr 1
  apply GeneralLinearGroup.ext
  intro row column
  rfl

theorem matrixApartment_singular (matrix : Matrix (Fin 3) (Fin 3) ℚ)
    (singular : matrix.det = 0) : matrixApartment matrix = 0 := by
  simp [matrixApartment, singular]

def cycleColumns (matrix : Matrix (Fin 3) (Fin 3) ℚ) : Matrix (Fin 3) (Fin 3) ℚ :=
  fun row column => matrix row (column + 1)

theorem cycleColumns_det (matrix : Matrix (Fin 3) (Fin 3) ℚ) :
    (cycleColumns matrix).det = matrix.det := by
  simp [Matrix.det_fin_three, cycleColumns]
  ring

theorem cycleColumns_frame (frame : RationalGL3) :
    cycleColumns frame.val = (frame * Adelic.weyl).val := by
  ext row column
  fin_cases column <;>
    simp [cycleColumns, Adelic.weyl, Matrix.mul_apply, Fin.sum_univ_three]

theorem matrixApartment_cycle (matrix : Matrix (Fin 3) (Fin 3) ℚ) :
    matrixApartment (cycleColumns matrix) = matrixApartment matrix := by
  by_cases nonzero : matrix.det ≠ 0
  · let frame := GeneralLinearGroup.mkOfDetNeZero matrix nonzero
    change matrixApartment (cycleColumns frame.val) = matrixApartment frame.val
    rw [cycleColumns_frame, matrixApartment_frame, matrixApartment_frame,
      ← apartment_translate, apartment_cyclic_relation, apartment_translate, mul_one]
  · rw [matrixApartment_singular matrix (not_ne_iff.mp nonzero),
      matrixApartment_singular _ (by simpa only [cycleColumns_det] using not_ne_iff.mp nonzero)]

theorem cycleColumns_update_zero (matrix : Matrix (Fin 3) (Fin 3) ℚ) (vector : Fin 3 → ℚ) :
    (cycleColumns matrix).updateCol 2 vector = cycleColumns (matrix.updateCol 0 vector) := by
  ext row column
  fin_cases column <;> simp [cycleColumns]

theorem cycleColumns_update_one (matrix : Matrix (Fin 3) (Fin 3) ℚ) (vector : Fin 3 → ℚ) :
    (cycleColumns matrix).updateCol 0 vector = cycleColumns (matrix.updateCol 1 vector) := by
  ext row column
  fin_cases column <;> simp [cycleColumns]

theorem cycleColumns_update_two (matrix : Matrix (Fin 3) (Fin 3) ℚ) (vector : Fin 3 → ℚ) :
    (cycleColumns matrix).updateCol 1 vector = cycleColumns (matrix.updateCol 2 vector) := by
  ext row column
  fin_cases column <;> simp [cycleColumns]

theorem rational_updateCol_det_formula (frame : RationalGL3) (vector weights : Fin 3 → ℚ)
    (combination : frame.val *ᵥ weights = vector) (column : Fin 3) :
    (frame.val.updateCol column vector).det = weights column * frame.val.det := by
  have vector_eq : vector = fun row => ∑ index, weights index • frame.val row index := by
    rw [← combination]
    funext row
    simp [Matrix.mulVec, dotProduct, mul_comm]
  rw [vector_eq, Matrix.det_updateCol_sum, smul_eq_mul]

end TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers
