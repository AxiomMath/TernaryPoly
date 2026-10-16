module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Real.DualHeightFormula
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Plane.LeviMultiplication

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

theorem integralRealGroup_planeLevi_corner (binary : GeneralLinearGroup (Fin 2) ℤ) (matrix : RealGL3) :
    (integralRealGroup (planeLevi binary 1) * matrix).val 2 2 = matrix.val 2 2 := by
  simp [integralRealGroup, planeLevi, planeBlock, Matrix.mul_apply, Fin.sum_univ_three]

theorem realPlaneHeight_integral_binary (binary : GeneralLinearGroup (Fin 2) ℤ) (matrix : RealGL3) :
    realPlaneHeight (integralRealGroup (planeLevi binary 1) * matrix) = realPlaneHeight matrix := by
  simp [realPlaneHeight, integralRealGroup, planeLevi, planeBlock,
    Matrix.mul_apply, Fin.sum_univ_three]

theorem integral_binary_plane_parabolic (binary : GeneralLinearGroup (Fin 2) ℤ)
    (matrix : RealGL3) (parabolic : InPlaneParabolic matrix) :
    InPlaneParabolic (integralRealGroup (planeLevi binary 1) * matrix) := by
  exact inPlane_mul (inPlane_map (Int.castRingHom ℝ) _ (planeLevi_mem binary 1)) parabolic

theorem integralRealGroup_mul_abs_det (integral : IntegralGL3) (matrix : RealGL3) :
    |(integralRealGroup integral * matrix).val.det| = |matrix.val.det| := by
  change |((integralRealGroup integral).val * matrix.val).det| = _
  rw [Matrix.det_mul, abs_mul, integralRealGroup_abs_det, one_mul]

theorem integral_binary_projected_minimum (matrix : RealGL3) (parabolic : InPlaneParabolic matrix) :
    ∃ binary : GeneralLinearGroup (Fin 2) ℤ, ∀ other : GeneralLinearGroup (Fin 2) ℤ,
      (integralRealGroup (planeLevi binary 1) * matrix).val 1 0 ^ 2 +
        (integralRealGroup (planeLevi binary 1) * matrix).val 1 1 ^ 2 ≤
      (integralRealGroup (planeLevi other 1) * matrix).val 1 0 ^ 2 +
        (integralRealGroup (planeLevi other 1) * matrix).val 1 1 ^ 2 := by
  obtain ⟨binary, minimal⟩ := integral_binary_dual_height_minimum matrix
  refine ⟨binary, ?_⟩
  intro other
  exact (realDualHeight_comparison _ _
    (integral_binary_plane_parabolic binary matrix parabolic)
    (integral_binary_plane_parabolic other matrix parabolic)
    (by rw [integralRealGroup_mul_abs_det, integralRealGroup_mul_abs_det])
    (by rw [integralRealGroup_planeLevi_corner, integralRealGroup_planeLevi_corner])).mp (minimal other)

theorem integral_binary_plane_height_minimum (matrix : RealGL3)
    (minimal : ∀ integral : IntegralGL3,
      realPlaneHeight matrix ≤ realPlaneHeight (integralRealGroup integral * matrix))
    (binary : GeneralLinearGroup (Fin 2) ℤ) :
    ∀ integral : IntegralGL3,
      realPlaneHeight (integralRealGroup (planeLevi binary 1) * matrix) ≤
        realPlaneHeight (integralRealGroup integral * (integralRealGroup (planeLevi binary 1) * matrix)) := by
  intro integral
  rw [realPlaneHeight_integral_binary]
  simpa only [map_mul, mul_assoc] using minimal (integral * planeLevi binary 1)

theorem integral_real_plane_two_minima (matrix : RealGL3) :
    ∃ integral : IntegralGL3, ∃ rotation : RealGL3,
      rotation.val.transpose * rotation.val = 1 ∧
      InPlaneParabolic (integralRealGroup integral * matrix * rotation) ∧
      0 < (integralRealGroup integral * matrix * rotation).val 2 2 ∧
      (∀ other : IntegralGL3,
        realPlaneHeight (integralRealGroup integral * matrix * rotation) ≤
          realPlaneHeight (integralRealGroup other * (integralRealGroup integral * matrix * rotation))) ∧
      (∀ binary : GeneralLinearGroup (Fin 2) ℤ,
        (integralRealGroup integral * matrix * rotation).val 1 0 ^ 2 +
          (integralRealGroup integral * matrix * rotation).val 1 1 ^ 2 ≤
        (integralRealGroup (planeLevi binary 1) * (integralRealGroup integral * matrix * rotation)).val 1 0 ^ 2 +
          (integralRealGroup (planeLevi binary 1) * (integralRealGroup integral * matrix * rotation)).val 1 1 ^ 2) := by
  obtain ⟨first, rotation, orthogonal, parabolic, positive, first_minimal⟩ :=
    integral_real_plane_minimal_decomposition matrix
  let intermediate := integralRealGroup first * matrix * rotation
  obtain ⟨binary, second_minimal⟩ := integral_binary_projected_minimum intermediate parabolic
  have combined : integralRealGroup (planeLevi binary 1 * first) * matrix * rotation =
      integralRealGroup (planeLevi binary 1) * intermediate := by
    simp only [intermediate, map_mul, mul_assoc]
  refine ⟨planeLevi binary 1 * first, rotation, orthogonal, ?_, ?_, ?_, ?_⟩
  · rw [combined]
    exact integral_binary_plane_parabolic binary intermediate parabolic
  · rw [combined, integralRealGroup_planeLevi_corner]
    exact positive
  · rw [combined]
    exact integral_binary_plane_height_minimum intermediate first_minimal binary
  · rw [combined]
    intro other
    have comparison := second_minimal (other * binary)
    simpa only [planeLevi_binary_mul, map_mul, mul_assoc] using comparison

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
