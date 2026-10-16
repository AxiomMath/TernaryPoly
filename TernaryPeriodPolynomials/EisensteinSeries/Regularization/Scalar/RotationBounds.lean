module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Scalar.RotationProjection

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

theorem cuspScalarCircleOrbit_norm_le (cusp : CuspidalRepresentation) (argument : BinaryAdelicGL)
    (vector : cusp.smooth) :
    ‖cuspScalarCircleOrbit cusp argument vector‖ ≤ ‖cuspBoundedRealization cusp vector‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
  intro angle
  exact cusp_realize_norm_le cusp vector _

theorem cuspBoundedRealization_projection_norm_le (cusp : CuspidalRepresentation) (weight : ℤ)
    (vector : cusp.smooth) :
    ‖cuspBoundedRealization cusp (cuspSmoothRotationProjection cusp weight vector)‖ ≤
      ‖cuspBoundedRealization cusp vector‖ := by
  apply BoundedContinuousFunction.norm_le_of_nonempty.mpr
  intro argument
  rw [cuspBoundedRealization_apply, cusp_realize_rotation_projection]
  exact (circleFourierCoefficient_norm_le weight (cuspScalarCircleOrbit cusp argument vector)).trans
    (cuspScalarCircleOrbit_norm_le cusp argument vector)

theorem cuspBoundedRealization_projection_weighted_norm_le (cusp : CuspidalRepresentation) (weight : ℤ)
    (order : ℕ) (vector : cusp.smooth) :
    |(weight : ℝ)| ^ order * ‖cuspBoundedRealization cusp (cuspSmoothRotationProjection cusp weight vector)‖ ≤
      ‖cuspBoundedRealization cusp ((cuspRotationOperator cusp ^ order) vector)‖ := by
  have projection := congrArg (fun smoothVector => ‖cuspBoundedRealization cusp smoothVector‖)
    (cuspSmoothRotationProjection_generator_pow cusp weight order vector)
  simp only [map_smul, norm_smul, norm_pow, norm_mul, Complex.norm_I, one_mul, Complex.norm_intCast] at projection
  rw [← projection]
  exact cuspBoundedRealization_projection_norm_le cusp weight ((cuspRotationOperator cusp ^ order) vector)

theorem cuspBoundedRealization_projection_norm_summable (cusp : CuspidalRepresentation) (vector : cusp.smooth) :
    Summable (fun weight : ℤ => ‖cuspBoundedRealization cusp (cuspSmoothRotationProjection cusp weight vector)‖) := by
  have majorant := integer_inverse_square_summable.mul_left
    ‖cuspBoundedRealization cusp ((cuspRotationOperator cusp ^ 2) vector)‖
  apply majorant.of_norm_bounded_eventually
  filter_upwards [Filter.eventually_cofinite_ne (0 : ℤ)] with weight nonzero
  rw [norm_norm]
  have positive : 0 < |(weight : ℝ)| ^ 2 := pow_pos (abs_pos.mpr (by exact_mod_cast nonzero)) _
  have bound := cuspBoundedRealization_projection_weighted_norm_le cusp weight 2 vector
  calc
    _ ≤ ‖cuspBoundedRealization cusp ((cuspRotationOperator cusp ^ 2) vector)‖ / |(weight : ℝ)| ^ 2 := by
      apply (le_div_iff₀ positive).mpr
      simpa only [mul_comm] using bound
    _ = _ := by ring

theorem cuspBoundedRealization_projection_summable (cusp : CuspidalRepresentation) (vector : cusp.smooth) :
    Summable (fun weight : ℤ => cuspBoundedRealization cusp (cuspSmoothRotationProjection cusp weight vector)) :=
  (cuspBoundedRealization_projection_norm_summable cusp vector).of_norm

theorem cuspScalarRotationCoefficient_norm_summable (cusp : CuspidalRepresentation) (argument : BinaryAdelicGL)
    (vector : cusp.smooth) :
    Summable (fun weight : ℤ => ‖fourierCoeff (cuspScalarCircleOrbit cusp argument vector) weight‖) := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _
    (cuspBoundedRealization_projection_norm_summable cusp vector)
  intro weight
  rw [← cusp_realize_rotation_projection]
  exact cusp_realize_norm_le cusp (cuspSmoothRotationProjection cusp weight vector) argument

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
