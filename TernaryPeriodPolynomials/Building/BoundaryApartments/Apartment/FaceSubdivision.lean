module

public import TernaryPeriodPolynomials.Building.BoundaryApartments.Apartment.Subdivision

@[expose] public section


open GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers

open Matrix

theorem edge_eq_of_same_endpoints {first second : Edges}
    (planes : endpoint .plane first = endpoint .plane second)
    (lines : endpoint .line first = endpoint .line second) : first = second := by
  induction first using Quotient.inductionOn with
  | _ first =>
    induction second using Quotient.inductionOn with
    | _ second =>
      exact QuotientGroup.eq.mpr ⟨QuotientGroup.eq.mp planes, QuotientGroup.eq.mp lines⟩

theorem frame_inverse_mul_updated (frame : RationalGL3) (vector weights : Fin 3 → ℚ)
    (combination : frame.val *ᵥ weights = vector) (column : Fin 3)
    (determinant_nonzero : (frame.val.updateCol column vector).det ≠ 0) :
    (frame⁻¹ * GeneralLinearGroup.mkOfDetNeZero
      (frame.val.updateCol column vector) determinant_nonzero).val =
        (1 : Matrix (Fin 3) (Fin 3) ℚ).updateCol column weights := by
  change frame.inv * frame.val.updateCol column vector = _
  have inverse_product : frame.inv * frame.val = 1 := frame.inv_mul
  rw [Matrix.mul_updateCol, inverse_product, ← combination, Matrix.mulVec_mulVec,
    inverse_product, Matrix.one_mulVec]

theorem plane_flag_update_in_plane (frame : RationalGL3) (vector weights : Fin 3 → ℚ)
    (combination : frame.val *ᵥ weights = vector) (last_zero : weights 2 = 0) (column : Fin 3)
    (determinant_nonzero : (frame.val.updateCol column vector).det ≠ 0) :
    (QuotientGroup.mk frame : Flags .plane) = QuotientGroup.mk
      (GeneralLinearGroup.mkOfDetNeZero (frame.val.updateCol column vector) determinant_nonzero) := by
  apply QuotientGroup.eq.mpr
  change _ = 0 ∧ _ = 0
  rw [frame_inverse_mul_updated frame vector weights combination column determinant_nonzero]
  constructor <;> simp [Matrix.updateCol_apply, last_zero]

theorem framePair_subdivision_in_plane (frame : RationalGL3) (vector weights : Fin 3 → ℚ)
    (combination : frame.val *ᵥ weights = vector) (last_zero : weights 2 = 0)
    (first_nonzero : (frame.val.updateCol 0 vector).det ≠ 0)
    (second_nonzero : (frame.val.updateCol 1 vector).det ≠ 0) :
    framePair frame =
      framePair (GeneralLinearGroup.mkOfDetNeZero (frame.val.updateCol 0 vector) first_nonzero) +
      framePair (GeneralLinearGroup.mkOfDetNeZero (frame.val.updateCol 1 vector) second_nonzero) := by
  let first := GeneralLinearGroup.mkOfDetNeZero (frame.val.updateCol 0 vector) first_nonzero
  let second := GeneralLinearGroup.mkOfDetNeZero (frame.val.updateCol 1 vector) second_nonzero
  have first_plane : (QuotientGroup.mk frame : Flags .plane) = QuotientGroup.mk first :=
    plane_flag_update_in_plane frame vector weights combination last_zero 0 first_nonzero
  have second_plane : (QuotientGroup.mk frame : Flags .plane) = QuotientGroup.mk second :=
    plane_flag_update_in_plane frame vector weights combination last_zero 1 second_nonzero
  have original_first : (QuotientGroup.mk frame : Edges) = QuotientGroup.mk second := by
    apply edge_eq_of_same_endpoints
    · exact second_plane
    · apply line_flag_eq_of_column 1
      intro row
      simp [second]
  have original_second : (QuotientGroup.mk (frame * swapFirstTwo) : Edges) =
      QuotientGroup.mk (first * swapFirstTwo) := by
    apply edge_eq_of_same_endpoints
    · change (QuotientGroup.mk (frame * swapFirstTwo) : Flags .plane) =
        QuotientGroup.mk (first * swapFirstTwo)
      simpa only [plane_flag_swap] using first_plane
    · apply line_flag_eq_of_column 1
      intro row
      simp [frame_swap_firstColumn, first]
  have internal : (QuotientGroup.mk first : Edges) =
      QuotientGroup.mk (second * swapFirstTwo) := by
    apply edge_eq_of_same_endpoints
    · change (QuotientGroup.mk first : Flags .plane) = QuotientGroup.mk (second * swapFirstTwo)
      rw [plane_flag_swap]
      exact first_plane.symm.trans second_plane
    · apply line_flag_eq_of_column 1
      intro row
      simp [frame_swap_firstColumn, first, second]
  change framePair frame = framePair first + framePair second
  simp only [framePair, original_first, original_second, internal]
  abel

theorem apartment_subdivision_in_plane (frame : RationalGL3) (vector weights : Fin 3 → ℚ)
    (combination : frame.val *ᵥ weights = vector) (last_zero : weights 2 = 0)
    (first_nonzero : (frame.val.updateCol 0 vector).det ≠ 0)
    (second_nonzero : (frame.val.updateCol 1 vector).det ≠ 0) :
    apartment frame =
      apartment (GeneralLinearGroup.mkOfDetNeZero (frame.val.updateCol 0 vector) first_nonzero) +
      apartment (GeneralLinearGroup.mkOfDetNeZero (frame.val.updateCol 1 vector) second_nonzero) := by
  let first := GeneralLinearGroup.mkOfDetNeZero (frame.val.updateCol 0 vector) first_nonzero
  let second := GeneralLinearGroup.mkOfDetNeZero (frame.val.updateCol 1 vector) second_nonzero
  have original_first := framePair_subdivision_in_plane frame vector weights combination last_zero
    first_nonzero second_nonzero
  change framePair frame = framePair first + framePair second at original_first
  have original_second : framePair (first * Adelic.weyl) = framePair (frame * Adelic.weyl) := by
    apply framePair_eq_of_columns <;> intro row <;>
      simp [frame_weyl_firstColumn, frame_weyl_secondColumn, first]
  have original_third : framePair (second * Adelic.weyl ^ 2) = framePair (frame * Adelic.weyl ^ 2) := by
    apply framePair_eq_of_columns <;> intro row <;>
      simp [frame_weylSquared_firstColumn, frame_weylSquared_secondColumn, second]
  have internal : framePair (second * Adelic.weyl) = -framePair (first * Adelic.weyl ^ 2) := by
    apply framePair_reverse_of_columns <;> intro row <;>
      simp [frame_weyl_firstColumn, frame_weyl_secondColumn,
        frame_weylSquared_firstColumn, frame_weylSquared_secondColumn, first, second]
  change apartment frame = apartment first + apartment second
  simp only [apartment_eq_framePairs, original_second, original_third, internal]
  rw [original_first]
  abel

end TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers
