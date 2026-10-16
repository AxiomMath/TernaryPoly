module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Integral.PlaneMinima

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

noncomputable def realProjectedRowSq (matrix : RealGL3) : ℝ :=
  matrix.val 1 0 ^ 2 + matrix.val 1 1 ^ 2

theorem realProjectedRowSq_rotation (matrix : RealGL3) (cosine sine : ℝ)
    (unit : cosine ^ 2 + sine ^ 2 = 1) :
    realProjectedRowSq (matrix * firstRealRotation cosine sine unit) = realProjectedRowSq matrix := by
  simp only [realProjectedRowSq]
  simp [firstRealRotation, Matrix.mul_apply, Fin.sum_univ_three]
  calc
    _ = (matrix.val 1 0 ^ 2 + matrix.val 1 1 ^ 2) * (cosine ^ 2 + sine ^ 2) := by ring
    _ = _ := by rw [unit, mul_one]

theorem real_plane_projected_positive (matrix : RealGL3) (parabolic : InPlaneParabolic matrix) :
    0 < realProjectedRowSq matrix := by
  have nonnegative : 0 ≤ realProjectedRowSq matrix := by unfold realProjectedRowSq; positivity
  by_contra! not_positive
  have first_zero : matrix.val 1 0 = 0 := by
    change matrix.val 1 0 ^ 2 + matrix.val 1 1 ^ 2 ≤ 0 at not_positive
    nlinarith [sq_nonneg (matrix.val 1 1)]
  have second_zero : matrix.val 1 1 = 0 := by
    change matrix.val 1 0 ^ 2 + matrix.val 1 1 ^ 2 ≤ 0 at not_positive
    nlinarith [sq_nonneg (matrix.val 1 0)]
  apply matrix.det_ne_zero
  rw [real_plane_determinant matrix parabolic, first_zero, second_zero]
  ring

theorem real_plane_triangular_rotation (matrix : RealGL3) (parabolic : InPlaneParabolic matrix) :
    ∃ (cosine sine : ℝ) (unit : cosine ^ 2 + sine ^ 2 = 1),
      InPlaneParabolic (matrix * firstRealRotation cosine sine unit) ∧
      (matrix * firstRealRotation cosine sine unit).val 1 0 = 0 ∧
      0 < (matrix * firstRealRotation cosine sine unit).val 1 1 ∧
      (matrix * firstRealRotation cosine sine unit).val 2 2 = matrix.val 2 2 := by
  let radius := Real.sqrt (realProjectedRowSq matrix)
  have radius_positive : 0 < radius := Real.sqrt_pos.mpr (real_plane_projected_positive matrix parabolic)
  have radius_sq : radius ^ 2 = matrix.val 1 0 ^ 2 + matrix.val 1 1 ^ 2 :=
    Real.sq_sqrt (real_plane_projected_positive matrix parabolic).le
  have unit : (matrix.val 1 1 / radius) ^ 2 + (matrix.val 1 0 / radius) ^ 2 = 1 := by
    field_simp
    nlinarith
  refine ⟨matrix.val 1 1 / radius, matrix.val 1 0 / radius, unit, ?_, ?_, ?_, ?_⟩
  · constructor <;>
      simp [firstRealRotation, Matrix.mul_apply, Fin.sum_univ_three, parabolic.1, parabolic.2]
  · simp [firstRealRotation, Matrix.mul_apply, Fin.sum_univ_three]
    ring
  · have diagonal : (matrix * firstRealRotation (matrix.val 1 1 / radius) (matrix.val 1 0 / radius) unit).val 1 1 = radius := by
      simp [firstRealRotation, Matrix.mul_apply, Fin.sum_univ_three]
      field_simp
      nlinarith
    rw [diagonal]
    exact radius_positive
  · simp [firstRealRotation, Matrix.mul_apply, Fin.sum_univ_three]

theorem integral_real_triangular_two_minima (matrix : RealGL3) :
    ∃ integral : IntegralGL3, ∃ rotation : RealGL3,
      rotation.val.transpose * rotation.val = 1 ∧
      InPlaneParabolic (integralRealGroup integral * matrix * rotation) ∧
      (integralRealGroup integral * matrix * rotation).val 1 0 = 0 ∧
      0 < (integralRealGroup integral * matrix * rotation).val 1 1 ∧
      0 < (integralRealGroup integral * matrix * rotation).val 2 2 ∧
      (∀ other : IntegralGL3,
        realPlaneHeight (integralRealGroup integral * matrix * rotation) ≤
          realPlaneHeight (integralRealGroup other * (integralRealGroup integral * matrix * rotation))) ∧
      (∀ binary : GeneralLinearGroup (Fin 2) ℤ,
        realProjectedRowSq (integralRealGroup integral * matrix * rotation) ≤
          realProjectedRowSq (integralRealGroup (planeLevi binary 1) *
            (integralRealGroup integral * matrix * rotation))) := by
  obtain ⟨integral, rotation, orthogonal, parabolic, positive, first_minimal, second_minimal⟩ :=
    integral_real_plane_two_minima matrix
  let intermediate := integralRealGroup integral * matrix * rotation
  obtain ⟨cosine, sine, unit, triangular, first_zero, second_positive, last⟩ :=
    real_plane_triangular_rotation intermediate parabolic
  let correction := firstRealRotation cosine sine unit
  have correction_orthogonal := firstRealRotation_orthogonal cosine sine unit
  have combined : integralRealGroup integral * matrix * (rotation * correction) = intermediate * correction := by
    simp only [intermediate, mul_assoc]
  refine ⟨integral, rotation * correction, real_orthogonal_mul orthogonal correction_orthogonal, ?_⟩
  rw [combined]
  refine ⟨triangular, first_zero, second_positive, ?_, ?_, ?_⟩
  · change 0 < (intermediate * firstRealRotation cosine sine unit).val 2 2
    rw [last]
    exact positive
  · exact integral_plane_height_minimum_rotate intermediate correction correction_orthogonal first_minimal
  · intro binary
    change realProjectedRowSq (intermediate * firstRealRotation cosine sine unit) ≤
      realProjectedRowSq (integralRealGroup (planeLevi binary 1) *
        (intermediate * firstRealRotation cosine sine unit))
    rw [← mul_assoc, realProjectedRowSq_rotation, realProjectedRowSq_rotation]
    exact second_minimal binary

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
