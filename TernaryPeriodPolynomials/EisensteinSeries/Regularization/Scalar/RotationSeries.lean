module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Scalar.RotationBounds

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

theorem cuspScalarRotationCoefficient_hasSum (cusp : CuspidalRepresentation) (argument : BinaryAdelicGL)
    (vector : cusp.smooth) :
    HasSum (fun weight : ℤ => fourierCoeff (cuspScalarCircleOrbit cusp argument vector) weight)
      (cusp.realize vector argument) := by
  have coefficients := (cuspScalarRotationCoefficient_norm_summable cusp argument vector).of_norm
  have series := hasSum_fourier_series_of_summable (f := cuspScalarCircleOrbit cusp argument vector) coefficients
  have evaluated := (ContinuousMap.evalCLM ℂ (0 : AddCircle (1 : ℝ))).hasSum series
  simpa [ContinuousMap.evalCLM_apply, cuspScalarCircleOrbit_apply, binary_atInfinity_one] using evaluated

theorem cuspBoundedRealization_projection_tsum (cusp : CuspidalRepresentation) (vector : cusp.smooth) :
    (∑' weight : ℤ, cuspBoundedRealization cusp (cuspSmoothRotationProjection cusp weight vector)) =
      cuspBoundedRealization cusp vector := by
  ext argument
  have series := (cuspBoundedRealization_projection_summable cusp vector).hasSum
  have evaluated := (BoundedContinuousFunction.evalCLM ℂ argument).hasSum series
  have scalar_series := cuspScalarRotationCoefficient_hasSum cusp argument vector
  simp only [← cusp_realize_rotation_projection] at scalar_series
  exact evaluated.unique scalar_series

theorem cuspBoundedRealization_projection_hasSum (cusp : CuspidalRepresentation) (vector : cusp.smooth) :
    HasSum (fun weight : ℤ => cuspBoundedRealization cusp (cuspSmoothRotationProjection cusp weight vector))
      (cuspBoundedRealization cusp vector) := by
  simpa only [cuspBoundedRealization_projection_tsum cusp vector] using
    (cuspBoundedRealization_projection_summable cusp vector).hasSum

theorem cuspBoundedRealization_rotation_hasSum (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (parameter : ℝ) :
    HasSum (fun weight : ℤ => Complex.exp (Complex.I * (weight : ℂ) * (parameter : ℂ)) •
      cuspBoundedRealization cusp (cuspSmoothRotationProjection cusp weight vector))
      (cuspBoundedRealization cusp (cuspSmoothAction cusp (atInfinity (binaryRotationPath parameter)) vector)) := by
  have series := cuspBoundedRealization_projection_hasSum cusp
    (cuspSmoothAction cusp (atInfinity (binaryRotationPath parameter)) vector)
  have projected (weight : ℤ) :
      cuspSmoothRotationProjection cusp weight (cuspSmoothAction cusp (atInfinity (binaryRotationPath parameter)) vector) =
        Complex.exp (Complex.I * (weight : ℂ) * (parameter : ℂ)) • cuspSmoothRotationProjection cusp weight vector := by
    have circle := cuspSmoothRotationProjection_action cusp weight
      (((parameter / (2 * Real.pi) : ℝ)) : AddCircle (1 : ℝ)) vector
    simpa only [circle_normalized_toCircle, circle_fourier_normalized, binaryRotationPath] using circle
  simpa only [projected, map_smul] using series

theorem cuspBoundedRealization_rotation_tsum (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (parameter : ℝ) :
    (∑' weight : ℤ, Complex.exp (Complex.I * (weight : ℂ) * (parameter : ℂ)) •
      cuspBoundedRealization cusp (cuspSmoothRotationProjection cusp weight vector)) =
        cuspBoundedRealization cusp (cuspSmoothAction cusp (atInfinity (binaryRotationPath parameter)) vector) :=
  (cuspBoundedRealization_rotation_hasSum cusp vector parameter).tsum_eq

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
