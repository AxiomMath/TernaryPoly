module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Scalar.RotationBounds

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

noncomputable def boundedAdelicCircleOrbitLinear (argument : BinaryAdelicGL) :
    BoundedContinuousFunction BinaryAdelicGL ℂ →ₗ[ℂ] C(AddCircle (1 : ℝ), ℂ) where
  toFun function :=
    ⟨fun angle => function (argument * atInfinity (binaryCircleRotation angle.toCircle)),
      function.continuous.comp (continuous_const.mul (binary_atInfinity_continuous.comp
        (binaryCircleRotation_continuous.comp AddCircle.continuous_toCircle)))⟩
  map_add' _ _ := by ext angle; rfl
  map_smul' _ _ := by ext angle; rfl

noncomputable def boundedAdelicCircleOrbit (argument : BinaryAdelicGL) :
    BoundedContinuousFunction BinaryAdelicGL ℂ →L[ℂ] C(AddCircle (1 : ℝ), ℂ) :=
  (boundedAdelicCircleOrbitLinear argument).mkContinuous 1 (by
    intro function
    rw [one_mul]
    apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
    intro angle
    exact BoundedContinuousFunction.norm_coe_le_norm function _)

noncomputable def boundedAdelicFourierCoefficient (argument : BinaryAdelicGL) (weight : ℤ) :
    BoundedContinuousFunction BinaryAdelicGL ℂ →L[ℂ] ℂ :=
  (circleFourierCoefficientContinuous weight).comp (boundedAdelicCircleOrbit argument)

theorem boundedAdelicFourierCoefficient_realize (cusp : CuspidalRepresentation)
    (argument : BinaryAdelicGL) (weight : ℤ) (vector : cusp.smooth) :
    boundedAdelicFourierCoefficient argument weight (cuspBoundedRealization cusp vector) =
      cusp.realize (cuspSmoothRotationProjection cusp weight vector) argument :=
  (cusp_realize_rotation_projection cusp argument weight vector).symm

theorem boundedAdelicFourierCoefficient_zero (function : BoundedContinuousFunction BinaryAdelicGL ℂ)
    (zero : ∀ argument weight, boundedAdelicFourierCoefficient argument weight function = 0) : function = 0 := by
  apply DFunLike.ext
  intro argument
  change function argument = 0
  let profile := boundedAdelicCircleOrbit argument function
  have coefficients : fourierCoeff profile = fun _ => 0 := funext (zero argument)
  have summable : Summable (fourierCoeff profile) := by rw [coefficients]; exact summable_zero
  have series := hasSum_fourier_series_of_summable (f := profile) summable
  have zero_series : HasSum (fun _ : ℤ => (0 : C(AddCircle (1 : ℝ), ℂ))) profile := by
    convert! series using 1
    funext weight
    rw [congrFun coefficients weight]
    exact (zero_smul ℂ (fourier weight : C(AddCircle (1 : ℝ), ℂ))).symm
  have profile_zero : profile = 0 := zero_series.unique hasSum_zero
  have value := congrArg (fun map : C(AddCircle (1 : ℝ), ℂ) => map 0) profile_zero
  change function (argument * atInfinity (binaryCircleRotation ((0 : AddCircle (1 : ℝ)).toCircle))) = 0 at value
  simpa only [AddCircle.toCircle_zero, map_one, binary_atInfinity_one, mul_one] using value

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
