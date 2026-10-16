module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Reduced.TriangularBounds

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

def firstCoordinateSign (R : Type*) [CommRing R] : GL3 R :=
  ⟨!![-1, 0, 0; 0, 1, 0; 0, 0, 1], !![-1, 0, 0; 0, 1, 0; 0, 0, 1], by
    ext row column
    fin_cases row <;> fin_cases column <;> simp [Matrix.mul_apply, Fin.sum_univ_three], by
    ext row column
    fin_cases row <;> fin_cases column <;> simp [Matrix.mul_apply, Fin.sum_univ_three]⟩

theorem firstCoordinateSign_det (R : Type*) [CommRing R] :
    (firstCoordinateSign R).val.det = -1 := by
  simp [firstCoordinateSign, Matrix.det_fin_three]

theorem integralRealGroup_firstCoordinateSign :
    integralRealGroup (firstCoordinateSign ℤ) = firstCoordinateSign ℝ := by
  apply Units.ext
  ext row column
  fin_cases row <;> fin_cases column <;> simp [integralRealGroup, firstCoordinateSign]

theorem firstCoordinateSign_orthogonal :
    (firstCoordinateSign ℝ).val.transpose * (firstCoordinateSign ℝ).val = 1 := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [firstCoordinateSign, Matrix.mul_apply, Fin.sum_univ_three]

theorem realTriangularReduced_left_sign (matrix : RealGL3) (reduced : realTriangularReduced matrix) :
    realTriangularReduced (firstCoordinateSign ℝ * matrix) := by
  simpa [realTriangularReduced, InPlaneParabolic, firstCoordinateSign,
    Matrix.mul_apply, Fin.sum_univ_three] using reduced

theorem realTriangularReduced_right_sign (matrix : RealGL3) (reduced : realTriangularReduced matrix) :
    realTriangularReduced (matrix * firstCoordinateSign ℝ) := by
  simpa [realTriangularReduced, InPlaneParabolic, firstCoordinateSign,
    Matrix.mul_apply, Fin.sum_univ_three] using reduced

theorem realTriangularReduced_first_ne_zero (matrix : RealGL3) (reduced : realTriangularReduced matrix) :
    matrix.val 0 0 ≠ 0 := by
  rcases reduced with ⟨_, _, positive, _, _, _, _, bound, _⟩
  intro zero
  rw [zero] at bound
  nlinarith

theorem integral_real_reduced_det_one (matrix : RealGL3) :
    ∃ integral : IntegralGL3, ∃ rotation : RealGL3,
      integral.val.det = 1 ∧ rotation.val.transpose * rotation.val = 1 ∧
      realTriangularReduced (integralRealGroup integral * matrix * rotation) := by
  obtain ⟨integral, rotation, orthogonal, reduced⟩ := integral_real_reduced_triangular_decomposition matrix
  rcases Int.units_eq_one_or (GeneralLinearGroup.det integral) with positive | negative
  · refine ⟨integral, rotation, ?_, orthogonal, reduced⟩
    exact congrArg Units.val positive
  · refine ⟨firstCoordinateSign ℤ * integral, rotation, ?_, orthogonal, ?_⟩
    · change ((firstCoordinateSign ℤ).val * integral.val).det = 1
      rw [Matrix.det_mul, firstCoordinateSign_det]
      have negative_det : integral.val.det = -1 := congrArg Units.val negative
      rw [negative_det]
      norm_num
    · simpa only [map_mul, integralRealGroup_firstCoordinateSign, mul_assoc] using
        realTriangularReduced_left_sign _ reduced

theorem realTriangularReduced_positive_correction (matrix : RealGL3) (reduced : realTriangularReduced matrix) :
    ∃ correction : RealGL3, correction.val.transpose * correction.val = 1 ∧
      realTriangularReduced (matrix * correction) ∧ 0 < (matrix * correction).val 0 0 := by
  by_cases positive : 0 < matrix.val 0 0
  · exact ⟨1, by simp, by simpa using reduced, by simpa using positive⟩
  · have negative : matrix.val 0 0 < 0 :=
      lt_of_le_of_ne (le_of_not_gt positive) (realTriangularReduced_first_ne_zero matrix reduced)
    refine ⟨firstCoordinateSign ℝ, firstCoordinateSign_orthogonal,
      realTriangularReduced_right_sign matrix reduced, ?_⟩
    simpa [firstCoordinateSign, Matrix.mul_apply, Fin.sum_univ_three] using neg_pos.mpr negative

theorem integral_real_positive_reduced_det_one (matrix : RealGL3) (determinant : matrix.val.det = 1) :
    ∃ integral : IntegralGL3, ∃ rotation : RealGL3,
      integral.val.det = 1 ∧ rotation.val.det = 1 ∧ rotation.val.transpose * rotation.val = 1 ∧
      realTriangularReduced (integralRealGroup integral * matrix * rotation) ∧
      0 < (integralRealGroup integral * matrix * rotation).val 0 0 := by
  obtain ⟨integral, rotation, integral_det, orthogonal, reduced⟩ := integral_real_reduced_det_one matrix
  obtain ⟨correction, correction_orthogonal, corrected, positive⟩ :=
    realTriangularReduced_positive_correction (integralRealGroup integral * matrix * rotation) reduced
  have combined_orthogonal := real_orthogonal_mul orthogonal correction_orthogonal
  have combined_reduced : realTriangularReduced (integralRealGroup integral * matrix * (rotation * correction)) := by
    simpa only [mul_assoc] using corrected
  have combined_positive : 0 < (integralRealGroup integral * matrix * (rotation * correction)).val 0 0 := by
    simpa only [mul_assoc] using positive
  refine ⟨integral, rotation * correction, integral_det, ?_, combined_orthogonal, combined_reduced, combined_positive⟩
  have real_integral_det : (integralRealGroup integral).val.det = 1 := by
    change (GeneralLinearGroup.det (integralRealGroup integral)).val = 1
    rw [integralRealGroup, GeneralLinearGroup.map_det]
    change (integral.val.det : ℝ) = 1
    rw [integral_det]
    norm_num
  have product_det : (integralRealGroup integral * matrix * (rotation * correction)).val.det =
      (rotation * correction).val.det := by
    change (((integralRealGroup integral).val * matrix.val) * (rotation * correction).val).det = _
    rw [Matrix.det_mul, Matrix.det_mul, real_integral_det, determinant, one_mul, one_mul]
  have product_positive : 0 < (integralRealGroup integral * matrix * (rotation * correction)).val.det := by
    rw [real_plane_determinant _ combined_reduced.1, combined_reduced.2.1]
    simpa only [mul_zero, sub_zero] using
      mul_pos (mul_pos combined_positive combined_reduced.2.2.1) combined_reduced.2.2.2.1
  rw [product_det] at product_positive
  have absolute := realOrthogonal_abs_det (rotation * correction) combined_orthogonal
  simpa only [abs_of_pos product_positive] using absolute

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
