module

public import TernaryPeriodPolynomials.Building.BoundaryApartments.UnimodularSubdivisionRelations

@[expose] public section


open GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers

open Matrix

theorem normalizedChange_sum_mulVec (change : normalizedFrameChanges) (vector : Fin 3 → ℤ) :
    ((∑ row, (change.val.val *ᵥ vector) row : ℤ) : ZMod 3) = ((∑ row, vector row : ℤ) : ZMod 3) := by
  have columns (column : Fin 3) : ∑ row, (change.val.val row column : ZMod 3) = 1 := by
    have entry := congrFun change.property column
    change (∑ row, 1 * (change.val.val row column : ZMod 3)) = 1 at entry
    simpa only [one_mul] using entry
  simp only [Matrix.mulVec, dotProduct, Int.cast_sum, Int.cast_mul]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_mul, columns, one_mul]

theorem integralFrame_updateCol_det (frame : IntegralGL3) (vector weights : Fin 3 → ℤ)
    (combination : frame.val *ᵥ weights = vector) (column : Fin 3) :
    (frame.val.updateCol column vector).det = weights column * frame.val.det := by
  have vector_eq : vector = fun row => ∑ index, weights index • frame.val row index := by
    rw [← combination]
    funext row
    simp [Matrix.mulVec, dotProduct, mul_comm]
  rw [vector_eq, Matrix.det_updateCol_sum, smul_eq_mul]

theorem integralFrame_abs_det (frame : IntegralGL3) : |frame.val.det| = 1 := by
  change |(GeneralLinearGroup.det frame : ℤ)| = 1
  rcases Int.units_eq_one_or (GeneralLinearGroup.det frame) with same | same <;>
    rw [same] <;> norm_num

/-- A tetrahedral subdivision whose faces are unimodular or singular is
already a consequence of the displayed apartment relations. -/
theorem normalizedMatrixClass_unimodular_subdivision (base : rationalLevel)
    (frame : normalizedFrameChanges) (vector : Fin 3 → ℤ)
    (normalized : ((∑ row, vector row : ℤ) : ZMod 3) = 1)
    (faces_small : ∀ column, |(frame.val.val.updateCol column vector).det| ≤ 1) :
    normalizedMatrixClass base frame.val.val =
      normalizedMatrixClass base (frame.val.val.updateCol 0 vector) +
      normalizedMatrixClass base (frame.val.val.updateCol 1 vector) +
      normalizedMatrixClass base (frame.val.val.updateCol 2 vector) := by
  let weights := frame.val.inv *ᵥ vector
  have combination : frame.val.val *ᵥ weights = vector := by
    simp only [weights, Matrix.mulVec_mulVec, frame.val.val_inv, Matrix.one_mulVec]
  have bounded (column : Fin 3) : |weights column| ≤ 1 := by
    have small := faces_small column
    rw [integralFrame_updateCol_det frame.val vector weights combination column,
      abs_mul, integralFrame_abs_det, mul_one] at small
    exact small
  have weights_normalized : ((weights 0 + weights 1 + weights 2 : ℤ) : ZMod 3) = 1 := by
    have sum := normalizedChange_sum_mulVec frame⁻¹ vector
    change ((∑ row, weights row : ℤ) : ZMod 3) = _ at sum
    simpa only [Fin.sum_univ_three] using sum.trans normalized
  have subdivision := unitFrameSubdivision_of_bounded weights bounded weights_normalized
    (base * normalizedFrameChangeMap frame)
  rw [← normalizedMatrixClass_left_mul base frame 1,
    ← normalizedMatrixClass_left_mul base frame ((1 : Matrix (Fin 3) (Fin 3) ℤ).updateCol 0 weights),
    ← normalizedMatrixClass_left_mul base frame ((1 : Matrix (Fin 3) (Fin 3) ℤ).updateCol 1 weights),
    ← normalizedMatrixClass_left_mul base frame ((1 : Matrix (Fin 3) (Fin 3) ℤ).updateCol 2 weights)] at subdivision
  simpa only [Matrix.mul_updateCol, Matrix.mul_one, combination] using subdivision

end TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers
