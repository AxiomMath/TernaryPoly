module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Compact.AnalyticAverage

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

noncomputable def binaryMatrixMultiplication :
    Matrix (Fin 2) (Fin 2) ℝ →L[ℝ] Matrix (Fin 2) (Fin 2) ℝ →L[ℝ] Matrix (Fin 2) (Fin 2) ℝ :=
  LinearMap.toContinuousLinearMap
    (LinearMap.toContinuousLinearMap.toLinearMap.comp (LinearMap.mul ℝ (Matrix (Fin 2) (Fin 2) ℝ)))

theorem binaryMatrixMultiplication_apply (first second : Matrix (Fin 2) (Fin 2) ℝ) :
    binaryMatrixMultiplication first second = first * second := rfl

noncomputable def binaryConjugationMap (matrix : BinaryRealGL) :
    Matrix (Fin 2) (Fin 2) ℝ →L[ℝ] Matrix (Fin 2) (Fin 2) ℝ :=
  (binaryMatrixMultiplication.flip matrix.val).comp (binaryMatrixMultiplication matrix.inv)

theorem binaryConjugationMap_apply (matrix : BinaryRealGL) (vector : Matrix (Fin 2) (Fin 2) ℝ) :
    binaryConjugationMap matrix vector = matrix.inv * vector * matrix.val := rfl

theorem binaryConjugationMap_continuous : Continuous binaryConjugationMap := by
  have value : Continuous (fun matrix : BinaryRealGL => matrix.val) := Units.continuous_val
  have inverse : Continuous (fun matrix : BinaryRealGL => matrix.inv) := value.comp continuous_inv
  exact (binaryMatrixMultiplication.flip.continuous.comp value).clm_comp
    (binaryMatrixMultiplication.continuous.comp inverse)

theorem binaryRotationConjugation_bounded : ∃ bound : NNReal, ∀ angle : AddCircle (1 : ℝ),
    ‖binaryConjugationMap (binaryCircleRotation angle.toCircle)‖ ≤ bound := by
  have continuous : Continuous (fun angle : AddCircle (1 : ℝ) =>
      binaryConjugationMap (binaryCircleRotation angle.toCircle)) := binaryConjugationMap_continuous.comp
    (binaryCircleRotation_continuous.comp AddCircle.continuous_toCircle)
  obtain ⟨bound, bounded⟩ := isCompact_univ.exists_bound_of_continuousOn continuous.continuousOn
  refine ⟨⟨max bound 0, le_max_right _ _⟩, fun angle => ?_⟩
  exact (bounded angle (Set.mem_univ _)).trans (le_max_left _ _)

theorem binaryConjugationMap_one_add (matrix : BinaryRealGL) (vector : Matrix (Fin 2) (Fin 2) ℝ) :
    binaryConjugationMap matrix (1 + vector) = 1 + binaryConjugationMap matrix vector := by
  simp only [binaryConjugationMap_apply, mul_add, add_mul, mul_one, matrix.inv_val]

theorem binaryConjugationMap_det (matrix : BinaryRealGL) (vector : Matrix (Fin 2) (Fin 2) ℝ) :
    (binaryConjugationMap matrix vector).det = vector.det := by
  simp only [binaryConjugationMap_apply, Matrix.det_mul]
  calc
    _ = (matrix.inv.det * matrix.val.det) * vector.det := by ring
    _ = vector.det := by rw [← Matrix.det_mul, matrix.inv_val, Matrix.det_one, one_mul]

theorem invertibleMatrix_conjugation (matrix : BinaryRealGL) (vector : Matrix (Fin 2) (Fin 2) ℝ) :
    invertibleMatrix (binaryConjugationMap matrix vector) = matrix⁻¹ * invertibleMatrix vector * matrix := by
  by_cases invertible : vector.det ≠ 0
  · have conjugate : (binaryConjugationMap matrix vector).det ≠ 0 := by
      rw [binaryConjugationMap_det]
      exact invertible
    apply Units.ext
    simp only [invertibleMatrix, dite_eq_left invertible, dite_eq_left conjugate,
      GeneralLinearGroup.val_mkOfDetNeZero, Units.val_mul]
    rfl
  · simp only [invertibleMatrix, binaryConjugationMap_det, dite_eq_right invertible, mul_one, inv_mul_cancel]

theorem invertibleMatrix_one_add_conjugation (matrix : BinaryRealGL) (vector : Matrix (Fin 2) (Fin 2) ℝ) :
    matrix * invertibleMatrix (1 + binaryConjugationMap matrix vector) = invertibleMatrix (1 + vector) * matrix := by
  rw [← binaryConjugationMap_one_add, invertibleMatrix_conjugation]
  simp only [← mul_assoc, mul_inv_cancel, one_mul]

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
