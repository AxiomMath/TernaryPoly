module

public import TernaryPeriodPolynomials.Building.BoundaryApartments.AffineBuilding

@[expose] public section


open GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers

open Matrix

def affineTriangleMatrix (first second third : AffinePoint) : Matrix (Fin 3) (Fin 3) ℚ :=
  !![first 0,second 0,third 0;first 1,second 1,third 1;1,1,1]

theorem affineTriangleMatrix_columns (first second third : AffinePoint) (row : Fin 3) :
    affineTriangleMatrix first second third row 0 = affineVector first row ∧
      affineTriangleMatrix first second third row 1 = affineVector second row ∧
      affineTriangleMatrix first second third row 2 = affineVector third row := by
  fin_cases row <;> exact ⟨rfl, rfl, rfl⟩

theorem affine_in_plane_replacements (frame : RationalGL3) (first second third : AffinePoint)
    (first_column : ∀ row, frame.val row 0 = affineVector first row)
    (second_column : ∀ row, frame.val row 1 = affineVector second row)
    (weights : Fin 3 → ℚ) (combination : frame.val *ᵥ weights = affineVector third)
    (last_zero : weights 2 = 0) (first_different : third ≠ first) (second_different : third ≠ second) :
    (frame.val.updateCol 0 (affineVector third)).det ≠ 0 ∧
      (frame.val.updateCol 1 (affineVector third)).det ≠ 0 := by
  have weight_sum : weights 0 + weights 1 = 1 := by
    have entry := congrFun combination 2
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three, first_column,
      second_column, affineVector, last_zero] using entry
  have formula := rational_updateCol_det_formula frame (affineVector third) weights combination
  constructor
  · intro zero_det
    rw [formula] at zero_det
    have first_zero := (mul_eq_zero.mp zero_det).resolve_right (rationalFrame_det_nonzero frame)
    have second_one : weights 1 = 1 := by linarith
    apply second_different
    apply affineVector_injective
    ext row
    have entry := congrFun combination row
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three, first_zero,
      second_one, last_zero, second_column] using entry.symm
  · intro zero_det
    rw [formula] at zero_det
    have second_zero := (mul_eq_zero.mp zero_det).resolve_right (rationalFrame_det_nonzero frame)
    have first_one : weights 0 = 1 := by linarith
    apply first_different
    apply affineVector_injective
    ext row
    have entry := congrFun combination row
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three, second_zero,
      first_one, last_zero, first_column] using entry.symm

theorem affinePair_triangle_singular (first second third : AffinePoint)
    (singular : (affineTriangleMatrix first second third).det = 0) :
    affinePair first second + affinePair second third + affinePair third first = 0 := by
  by_cases first_second : first = second
  · subst second
    rw [affinePair_self, zero_add, affinePair_reverse first third, add_neg_cancel]
  by_cases third_first : third = first
  · subst third
    rw [affinePair_self, affinePair_reverse first second, add_neg_cancel, add_zero]
  by_cases third_second : third = second
  · subst third
    rw [affinePair_self, add_zero, affinePair_reverse first second, add_neg_cancel]
  let frame := affinePairFrame first second first_second
  have first_column := (affinePairFrame_columns first second first_second).1
  have second_column := (affinePairFrame_columns first second first_second).2
  let weights := frame.inv *ᵥ affineVector third
  have combination : frame.val *ᵥ weights = affineVector third := by
    simp only [weights, Matrix.mulVec_mulVec, frame.val_inv, Matrix.one_mulVec]
  have updated : frame.val.updateCol 2 (affineVector third) =
      affineTriangleMatrix first second third := by
    ext row column
    fin_cases column
    · change frame.val row 0 = affineTriangleMatrix first second third row 0
      exact (first_column row).trans (affineTriangleMatrix_columns first second third row).1.symm
    · change frame.val row 1 = affineTriangleMatrix first second third row 1
      exact (second_column row).trans (affineTriangleMatrix_columns first second third row).2.1.symm
    · exact (affineTriangleMatrix_columns first second third row).2.2.symm
  have last_zero : weights 2 = 0 := by
    rw [← updated, rational_updateCol_det_formula frame _ weights combination 2] at singular
    exact (mul_eq_zero.mp singular).resolve_right (rationalFrame_det_nonzero frame)
  obtain ⟨first_nonzero, second_nonzero⟩ := affine_in_plane_replacements frame first second third
    first_column second_column weights combination last_zero third_first third_second
  let first_frame := GeneralLinearGroup.mkOfDetNeZero
    (frame.val.updateCol 0 (affineVector third)) first_nonzero
  let second_frame := GeneralLinearGroup.mkOfDetNeZero
    (frame.val.updateCol 1 (affineVector third)) second_nonzero
  have first_pair : affinePair third second = framePair first_frame := by
    apply affinePair_frame
    · intro row
      simp [first_frame]
    · intro row
      simpa [first_frame] using second_column row
  have second_pair : affinePair first third = framePair second_frame := by
    apply affinePair_frame
    · intro row
      simpa [second_frame] using first_column row
    · intro row
      simp [second_frame]
  have subdivision := framePair_subdivision_in_plane frame (affineVector third) weights
    combination last_zero first_nonzero second_nonzero
  change framePair frame = framePair first_frame + framePair second_frame at subdivision
  rw [← affinePair_frame frame first second first_column second_column,
    ← first_pair, ← second_pair] at subdivision
  rw [subdivision, affinePair_reverse second third, affinePair_reverse first third]
  abel

theorem affinePair_triangle (first second third : AffinePoint) :
    affinePair first second + affinePair second third + affinePair third first =
      matrixApartment (affineTriangleMatrix first second third) := by
  by_cases singular : (affineTriangleMatrix first second third).det = 0
  · rw [matrixApartment_singular _ singular]
    exact affinePair_triangle_singular first second third singular
  let frame := GeneralLinearGroup.mkOfDetNeZero (affineTriangleMatrix first second third) singular
  change _ = matrixApartment frame.val
  rw [matrixApartment_frame, apartment_eq_framePairs]
  congr 2
  · apply affinePair_frame
    · intro row
      exact (affineTriangleMatrix_columns first second third row).1
    · intro row
      exact (affineTriangleMatrix_columns first second third row).2.1
  · apply affinePair_frame
    · intro row
      rw [frame_weyl_firstColumn]
      exact (affineTriangleMatrix_columns first second third row).2.1
    · intro row
      rw [frame_weyl_secondColumn]
      exact (affineTriangleMatrix_columns first second third row).2.2
  · apply affinePair_frame
    · intro row
      rw [frame_weylSquared_firstColumn]
      exact (affineTriangleMatrix_columns first second third row).2.2
    · intro row
      rw [frame_weylSquared_secondColumn]
      exact (affineTriangleMatrix_columns first second third row).1

end TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers
