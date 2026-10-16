module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Rotation.Kernel
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Scalar.Convolution
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Cusp.SupNorm

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RotationCircle TernaryPeriodPolynomials.PlaneEisensteinContinuation.RotationFourier TernaryPeriodPolynomials.PlaneEisensteinContinuation.RotationConvolution
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RotationRealization TernaryPeriodPolynomials.PlaneEisensteinContinuation.RotationKernel TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspSupNorm

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.RotationScalar

theorem smoothMode_convolution (data : CuspidalRepresentation) (kernel : C(Parameter, ℂ))
    (vector : data.smooth) (index : ℤ) :
    smoothMode data index (smoothConvolution data kernel vector) =
      fourierCoeff kernel (-index) • smoothMode data index vector :=
  Subtype.ext (modeVector_convolution data kernel vector.val index)

/-- Realization of a compact rotation convolution is its actual scalar Haar integral. -/
theorem realize_convolution (data : CuspidalRepresentation) (kernel : C(Parameter, ℂ))
    (vector : data.smooth) (point : BinaryAdelicGL) :
    data.realize (smoothConvolution data kernel vector) point =
      ∫ parameter : Parameter, kernel parameter *
        data.realize vector (point * atInfinity (rotation parameter)) ∂AddCircle.haarAddCircle := by
  have orbitEquality : scalarOrbit data point (smoothConvolution data kernel vector) =
      ScalarConvolution.convolution kernel (scalarOrbit data point vector) := by
    apply DFunLike.coe_injective
    apply FourierUniqueness.ext
      (scalarOrbit data point (smoothConvolution data kernel vector))
      (ScalarConvolution.convolution kernel (scalarOrbit data point vector))
      (scalarOrbit data point (smoothConvolution data kernel vector)).continuous
      (ScalarConvolution.convolution kernel (scalarOrbit data point vector)).continuous
    intro index
    rw [ScalarConvolution.convolution_fourierCoeff]
    change scalarCoefficient data point index (smoothConvolution data kernel vector) =
      fourierCoeff kernel (-index) * scalarCoefficient data point index vector
    rw [scalarCoefficient_eq_mode, scalarCoefficient_eq_mode, smoothMode_convolution, map_smul]
    rfl
  have atZero := congrArg (fun function : C(Parameter, ℂ) => function 0) orbitEquality
  rw [ScalarConvolution.convolution_apply] at atZero
  simpa only [scalarOrbit, LinearMap.coe_mk, AddHom.coe_mk, ContinuousMap.coe_mk,
    rotation_zero, TernaryPeriodPolynomials.PlaneEisensteinContinuation.AveragingSmooth.atInfinity_one, mul_one, add_zero] using atZero

theorem cuspSupNorm_smoothMode_le (data : CuspidalRepresentation) (index : ℤ)
    (vector : data.smooth) : cuspSupNorm (smoothMode data index vector) ≤ cuspSupNorm vector := by
  apply cuspSupNorm_le
  intro point
  rw [← scalarCoefficient_eq_mode]
  change ‖∫ parameter : Parameter, fourier (-index) parameter •
    data.realize vector (point * atInfinity (rotation parameter)) ∂AddCircle.haarAddCircle‖ ≤ _
  have estimate := norm_integral_le_of_norm_le_const (μ := AddCircle.haarAddCircle)
    (Filter.Eventually.of_forall (fun parameter : Parameter => show
      ‖fourier (-index) parameter • data.realize vector (point * atInfinity (rotation parameter))‖ ≤
        cuspSupNorm vector by
      rw [norm_smul, fourier_norm_one, one_mul]
      exact realize_le_cuspSupNorm vector _))
  simpa using estimate

theorem cuspSupNorm_convolution_le (data : CuspidalRepresentation) (kernel : C(Parameter, ℂ))
    (vector : data.smooth) :
    cuspSupNorm (smoothConvolution data kernel vector) ≤
      (∫ parameter : Parameter, ‖kernel parameter‖ ∂AddCircle.haarAddCircle) * cuspSupNorm vector := by
  apply cuspSupNorm_le
  intro point
  rw [realize_convolution]
  have kernelIntegrable : Integrable (fun parameter : Parameter => ‖kernel parameter‖) AddCircle.haarAddCircle :=
    kernel.continuous.norm.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have scalarIntegrable : Integrable (fun parameter : Parameter =>
      kernel parameter * data.realize vector (point * atInfinity (rotation parameter))) AddCircle.haarAddCircle :=
    (kernel.continuous.mul (scalarOrbit_continuous data point vector)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  calc
    _ ≤ ∫ parameter : Parameter,
        ‖kernel parameter * data.realize vector (point * atInfinity (rotation parameter))‖
          ∂AddCircle.haarAddCircle := norm_integral_le_integral_norm _
    _ ≤ ∫ parameter : Parameter, ‖kernel parameter‖ * cuspSupNorm vector ∂AddCircle.haarAddCircle := by
      apply integral_mono scalarIntegrable.norm (kernelIntegrable.mul_const _)
      intro parameter
      change ‖kernel parameter * data.realize vector (point * atInfinity (rotation parameter))‖ ≤
        ‖kernel parameter‖ * cuspSupNorm vector
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (realize_le_cuspSupNorm vector _) (norm_nonneg _)
    _ = _ := integral_mul_const _ _

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.RotationScalar
