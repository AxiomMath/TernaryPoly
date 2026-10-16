module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Cusp.Reflection

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem cohomological_lowest_weight_vector {cusp : CuspidalRepresentation} {degree : ℕ}
    (cohomological : Cohomological cusp degree) :
    ∃ vector : cusp.smooth, vector ≠ 0 ∧
      cuspRotationOperator cusp vector = (Complex.I * ((degree : ℂ) + 3)) • vector ∧
      cuspLoweringOperator cusp vector = 0 := by
  obtain ⟨weight, vector, nonzero, rotation, size, lowest, highest⟩ :=
    cohomological_extremal_rotation_weight cohomological
  rcases lt_or_ge weight 0 with negative | nonnegative
  · have negative_real : (weight : ℝ) < 0 := by exact_mod_cast negative
    rw [abs_of_neg negative_real] at size
    have weight_value : -(weight : ℂ) = (degree : ℂ) + 3 := by exact_mod_cast size
    refine ⟨cuspSmoothAction cusp (atInfinity binaryReflection) vector,
      cuspSmoothAction_ne_zero cusp _ vector nonzero, ?_, ?_⟩
    · rw [cuspRotation_reflection, rotation, map_smul, ← neg_smul, ← mul_neg, weight_value]
    · rw [cuspLowering_reflection, highest negative, map_zero]
  · have nonnegative_real : (0 : ℝ) ≤ weight := by exact_mod_cast nonnegative
    rw [abs_of_nonneg nonnegative_real] at size
    have positive_real : (0 : ℝ) < weight := by
      rw [size]
      positivity
    have positive : 0 < weight := by exact_mod_cast positive_real
    have weight_value : (weight : ℂ) = (degree : ℂ) + 3 := by exact_mod_cast size
    refine ⟨vector, nonzero, ?_, lowest positive⟩
    simpa only [weight_value] using rotation

theorem cohomological_highest_weight_vector {cusp : CuspidalRepresentation} {degree : ℕ}
    (cohomological : Cohomological cusp degree) :
    ∃ vector : cusp.smooth, vector ≠ 0 ∧
      cuspRotationOperator cusp vector = (-Complex.I * ((degree : ℂ) + 3)) • vector ∧
      cuspRaisingOperator cusp vector = 0 := by
  obtain ⟨vector, nonzero, rotation, lowest⟩ := cohomological_lowest_weight_vector cohomological
  refine ⟨cuspSmoothAction cusp (atInfinity binaryReflection) vector,
    cuspSmoothAction_ne_zero cusp _ vector nonzero, ?_, ?_⟩
  · rw [cuspRotation_reflection, rotation, map_smul, ← neg_smul, neg_mul]
  · rw [cuspRaising_reflection, lowest, map_zero]

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
