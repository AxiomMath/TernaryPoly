module

public import TernaryPeriodPolynomials.Building.BoundaryApartments.MatrixApartment

@[expose] public section


open GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers

open Matrix

theorem matrixApartment_single_replacement (frame : RationalGL3) (vector weights : Fin 3 → ℚ)
    (combination : frame.val *ᵥ weights = vector) (column : Fin 3)
    (only_column : ∀ index, index ≠ column → weights index = 0)
    (nonzero : (frame.val.updateCol column vector).det ≠ 0) :
    matrixApartment frame.val = matrixApartment (frame.val.updateCol column vector) := by
  have weights_eq : weights = Pi.single column (weights column) := by
    ext index
    by_cases same : index = column
    · subst index
      simp
    · simp [same, only_column index same]
  have vector_eq (row : Fin 3) : vector row = weights column * frame.val row column := by
    rw [← combination, weights_eq]
    simp [Matrix.mulVec, dotProduct, Pi.single_apply, mul_comm]
  let replacement := GeneralLinearGroup.mkOfDetNeZero (frame.val.updateCol column vector) nonzero
  change matrixApartment frame.val = matrixApartment replacement.val
  rw [matrixApartment_frame, matrixApartment_frame]
  apply apartment_eq_of_scaled_columns _ _ (Function.update (fun _ => 1) column (weights column))
  intro row index
  change (frame.val.updateCol column vector) row index = _
  by_cases same : index = column
  · subst index
    simp [vector_eq]
  · simp [Matrix.updateCol_ne same, Function.update_of_ne same]

theorem matrixApartment_subdivision_face (frame : RationalGL3) (vector : Fin 3 → ℚ)
    (vector_nonzero : vector ≠ 0) (last_zero : (frame.val.updateCol 2 vector).det = 0) :
    matrixApartment frame.val = matrixApartment (frame.val.updateCol 0 vector) +
      matrixApartment (frame.val.updateCol 1 vector) + matrixApartment (frame.val.updateCol 2 vector) := by
  let weights := frame.inv *ᵥ vector
  have combination : frame.val *ᵥ weights = vector := by
    simp only [weights, Matrix.mulVec_mulVec, frame.val_inv, Matrix.one_mulVec]
  have formula := rational_updateCol_det_formula frame vector weights combination
  have last_weight : weights 2 = 0 := by
    rw [formula] at last_zero
    exact (mul_eq_zero.mp last_zero).resolve_right (rationalFrame_det_nonzero frame)
  rw [matrixApartment_singular _ last_zero, add_zero]
  by_cases first_nonzero : (frame.val.updateCol 0 vector).det ≠ 0
  · by_cases second_nonzero : (frame.val.updateCol 1 vector).det ≠ 0
    · rw [matrixApartment_frame, matrixApartment, dite_eq_left first_nonzero,
        matrixApartment, dite_eq_left second_nonzero]
      exact apartment_subdivision_in_plane frame vector weights combination last_weight
        first_nonzero second_nonzero
    · have second_zero := not_ne_iff.mp second_nonzero
      have second_weight : weights 1 = 0 := by
        rw [formula] at second_zero
        exact (mul_eq_zero.mp second_zero).resolve_right (rationalFrame_det_nonzero frame)
      rw [matrixApartment_singular _ (not_ne_iff.mp second_nonzero), add_zero]
      apply matrixApartment_single_replacement frame vector weights combination 0 _ first_nonzero
      intro index different
      fin_cases index
      · exact (different rfl).elim
      · exact second_weight
      · exact last_weight
  · have first_zero := not_ne_iff.mp first_nonzero
    have first_weight : weights 0 = 0 := by
      rw [formula] at first_zero
      exact (mul_eq_zero.mp first_zero).resolve_right (rationalFrame_det_nonzero frame)
    rw [matrixApartment_singular _ (not_ne_iff.mp first_nonzero), zero_add]
    have second_nonzero : (frame.val.updateCol 1 vector).det ≠ 0 := by
      intro second_zero
      have second_weight : weights 1 = 0 := by
        rw [formula] at second_zero
        exact (mul_eq_zero.mp second_zero).resolve_right (rationalFrame_det_nonzero frame)
      have weights_zero : weights = 0 := by
        ext index
        fin_cases index <;> assumption
      apply vector_nonzero
      rw [← combination, weights_zero, Matrix.mulVec_zero]
    apply matrixApartment_single_replacement frame vector weights combination 1 _ second_nonzero
    intro index different
    fin_cases index
    · exact first_weight
    · exact (different rfl).elim
    · exact last_weight

theorem matrixApartment_subdivision (frame : RationalGL3) (vector : Fin 3 → ℚ)
    (vector_nonzero : vector ≠ 0) :
    matrixApartment frame.val = matrixApartment (frame.val.updateCol 0 vector) +
      matrixApartment (frame.val.updateCol 1 vector) + matrixApartment (frame.val.updateCol 2 vector) := by
  by_cases last_zero : (frame.val.updateCol 2 vector).det = 0
  · exact matrixApartment_subdivision_face frame vector vector_nonzero last_zero
  by_cases first_zero : (frame.val.updateCol 0 vector).det = 0
  · have rotated_zero : ((frame * Adelic.weyl).val.updateCol 2 vector).det = 0 := by
      rw [← cycleColumns_frame, cycleColumns_update_zero, cycleColumns_det, first_zero]
    have rotated := matrixApartment_subdivision_face (frame * Adelic.weyl) vector
      vector_nonzero rotated_zero
    rw [← cycleColumns_frame, cycleColumns_update_zero, cycleColumns_update_one,
      cycleColumns_update_two] at rotated
    simp only [matrixApartment_cycle] at rotated
    rw [rotated]
    abel
  by_cases second_zero : (frame.val.updateCol 1 vector).det = 0
  · have rotated_zero : (((frame * Adelic.weyl) * Adelic.weyl).val.updateCol 2 vector).det = 0 := by
      rw [← cycleColumns_frame, cycleColumns_update_zero, cycleColumns_det,
        ← cycleColumns_frame, cycleColumns_update_one, cycleColumns_det, second_zero]
    have rotated := matrixApartment_subdivision_face ((frame * Adelic.weyl) * Adelic.weyl)
      vector vector_nonzero rotated_zero
    rw [← cycleColumns_frame, cycleColumns_update_zero, cycleColumns_update_one,
      cycleColumns_update_two, ← cycleColumns_frame] at rotated
    simp only [matrixApartment_cycle, cycleColumns_update_zero,
      cycleColumns_update_one, cycleColumns_update_two] at rotated
    rw [rotated]
    abel
  rw [matrixApartment_frame, matrixApartment, dite_eq_left first_zero,
    matrixApartment, dite_eq_left second_zero, matrixApartment, dite_eq_left last_zero]
  exact apartment_subdivision_nondegenerate frame vector first_zero second_zero last_zero

end TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers
