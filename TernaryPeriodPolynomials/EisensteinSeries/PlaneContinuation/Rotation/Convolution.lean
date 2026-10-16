module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Rotation.Differentiation

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RotationCircle TernaryPeriodPolynomials.PlaneEisensteinContinuation.RotationFourier TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.ArchimedeanAveraging MeasureTheory

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.RotationConvolution

theorem modeVector_translate (data : CuspidalRepresentation) (index : ℤ) (vector : data.H) (parameter : Parameter) :
    modeVector data index (data.π (atInfinity (rotation parameter)) vector) =
      fourier index parameter • modeVector data index vector := by
  have curveEquality :
      (fun point : Parameter => data.π (atInfinity (rotation point))
        (data.π (atInfinity (rotation parameter)) vector)) =
      (fun point : Parameter => unitaryOperator data (atInfinity (rotation parameter))
        (data.π (atInfinity (rotation point)) vector)) := by
    funext point
    change data.π (atInfinity (rotation point)) (data.π (atInfinity (rotation parameter)) vector) =
      data.π (atInfinity (rotation parameter)) (data.π (atInfinity (rotation point)) vector)
    calc
      _ = data.π (atInfinity (rotation (point + parameter))) vector := by
        rw [rotation_add, TernaryPeriodPolynomials.PlaneEisensteinContinuation.Height.atInfinity_mul, map_mul, Module.End.mul_apply]
      _ = _ := by rw [add_comm, rotation_add, TernaryPeriodPolynomials.PlaneEisensteinContinuation.Height.atInfinity_mul, map_mul, Module.End.mul_apply]
  unfold modeVector
  rw [curveEquality, FourierUniqueness.map_fourierCoeff _ (orbit_continuous data vector)]
  exact modeVector_eigen data index vector parameter

theorem kernel_orbit_integrable (data : CuspidalRepresentation) (vector : data.H) (kernel : C(Parameter, ℂ)) :
    Integrable (fun point : Parameter => kernel point • data.π (atInfinity (rotation point)) vector)
      AddCircle.haarAddCircle :=
  (kernel.continuous.smul (orbit_continuous data vector)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

noncomputable def convolutionVector (data : CuspidalRepresentation) (kernel : C(Parameter, ℂ)) (vector : data.H) : data.H :=
  ∫ point : Parameter, kernel point • data.π (atInfinity (rotation point)) vector ∂AddCircle.haarAddCircle

theorem convolutionVector_preserves_fixedSmooth (data : CuspidalRepresentation) (kernel : C(Parameter, ℂ))
    (level : Subgroup BinaryFiniteGL) (openness : IsOpen (level : Set BinaryFiniteGL))
    (compactness : IsCompact (level : Set BinaryFiniteGL))
    (vector : data.smooth) (fixed : vector.val ∈ fixedSubspace data level) :
    convolutionVector data kernel vector.val ∈ data.smooth ∧
      convolutionVector data kernel vector.val ∈ fixedSubspace data level :=
  integrable_weighted_parameter_integral_mem data level openness compactness vector fixed
    rotation rotation_continuous AddCircle.haarAddCircle kernel
    (kernel.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))

theorem convolutionVector_mem_smooth (data : CuspidalRepresentation) (kernel : C(Parameter, ℂ))
    (vector : data.smooth) : convolutionVector data kernel vector.val ∈ data.smooth := by
  obtain ⟨level, openness, compactness, fixed⟩ := ((data.smooth_exact vector.val).mp vector.property).2
  exact (convolutionVector_preserves_fixedSmooth data kernel level openness compactness vector fixed).1

noncomputable def smoothConvolution (data : CuspidalRepresentation) (kernel : C(Parameter, ℂ))
    (vector : data.smooth) : data.smooth :=
  ⟨convolutionVector data kernel vector.val, convolutionVector_mem_smooth data kernel vector⟩

theorem modeVector_convolution (data : CuspidalRepresentation) (kernel : C(Parameter, ℂ))
    (vector : data.H) (index : ℤ) :
    modeVector data index (convolutionVector data kernel vector) =
      fourierCoeff kernel (-index) • modeVector data index vector := by
  have integralMap := (modeOperator data index).integral_comp_comm (kernel_orbit_integrable data vector kernel)
  change (∫ point : Parameter, modeOperator data index
      (kernel point • data.π (atInfinity (rotation point)) vector) ∂AddCircle.haarAddCircle) =
    modeVector data index (convolutionVector data kernel vector) at integralMap
  rw [← integralMap]
  calc
    _ = fourierCoeff (fun point : Parameter => kernel point • modeVector data index vector) (-index) := by
      unfold fourierCoeff
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun point => by
        change modeOperator data index (kernel point • data.π (atInfinity (rotation point)) vector) =
          fourier (- -index) point • (kernel point • modeVector data index vector)
        rw [map_smul, modeOperator_apply, modeVector_translate, neg_neg, smul_comm])
    _ = _ := FourierUniqueness.fourierCoeff_smul_vector kernel kernel.continuous _ (-index)

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.RotationConvolution
