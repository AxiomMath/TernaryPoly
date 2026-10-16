module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.QuadraticRotationDivisors

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem cusp_realize_rotation_projection (cusp : CuspidalRepresentation) (argument : BinaryAdelicGL)
    (weight : ℤ) (vector : cusp.smooth) :
    cusp.realize (cuspSmoothRotationProjection cusp weight vector) argument =
      fourierCoeff (cuspScalarCircleOrbit cusp argument vector) weight :=
  cusp_realize_projection_of_small_divisor_bound cusp argument weight
    ((Real.sqrt 2 : ℝ) : AddCircle (1 : ℝ)) quadratic_rotation_nonresonant 5
    quadratic_rotation_inverse_bound vector

theorem cuspScalarRotationCoefficient_generator (cusp : CuspidalRepresentation) (argument : BinaryAdelicGL)
    (weight : ℤ) (vector : cusp.smooth) :
    cuspScalarRotationCoefficient cusp argument weight (cuspRotationOperator cusp vector) =
      (Complex.I * (weight : ℂ)) * cuspScalarRotationCoefficient cusp argument weight vector := by
  rw [cuspScalarRotationCoefficient_apply, ← cusp_realize_rotation_projection,
    cuspSmoothRotationProjection_generator, map_smul, Pi.smul_apply, smul_eq_mul,
    cusp_realize_rotation_projection, cuspScalarRotationCoefficient_apply]

theorem cuspScalarRotationCoefficient_generator_pow (cusp : CuspidalRepresentation) (argument : BinaryAdelicGL)
    (weight : ℤ) (order : ℕ) (vector : cusp.smooth) :
    cuspScalarRotationCoefficient cusp argument weight ((cuspRotationOperator cusp ^ order) vector) =
      (Complex.I * (weight : ℂ)) ^ order * cuspScalarRotationCoefficient cusp argument weight vector := by
  rw [cuspScalarRotationCoefficient_apply, ← cusp_realize_rotation_projection,
    cuspSmoothRotationProjection_generator_pow, map_smul, Pi.smul_apply, smul_eq_mul,
    cusp_realize_rotation_projection, cuspScalarRotationCoefficient_apply]

theorem cohomological_scalar_rotation_spectrum {cusp : CuspidalRepresentation} {degree : ℕ}
    (cohomological : Cohomological cusp degree) (argument : BinaryAdelicGL) (weight : ℤ)
    (forbidden : ¬ ∃ step : ℕ, weight.natAbs = degree + 3 + 2 * step) (vector : cusp.smooth) :
    fourierCoeff (cuspScalarCircleOrbit cusp argument vector) weight = 0 := by
  rw [← cusp_realize_rotation_projection]
  have zero : cuspSmoothRotationProjection cusp weight vector = 0 :=
    Subtype.ext (cohomological_hilbert_projection_spectrum cohomological weight forbidden vector.val)
  rw [zero, map_zero, Pi.zero_apply]

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
