module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Rotation.Difference
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Scalar.FourierOperator
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Smooth

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RotationCircle TernaryPeriodPolynomials.PlaneEisensteinContinuation.RotationFourier TernaryPeriodPolynomials.PlaneEisensteinContinuation.RotationDifference
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.ScalarFourierOperator TernaryPeriodPolynomials.PlaneEisensteinContinuation.FourierDifferentiation

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.RotationRealization

theorem scalarOrbit_continuous (data : CuspidalRepresentation) (point : BinaryAdelicGL) (vector : data.smooth) :
    Continuous (fun parameter : Parameter => data.realize vector (point * atInfinity (rotation parameter))) := by
  have smoothContinuity := TernaryPeriodPolynomials.PlaneEisensteinContinuation.Smooth.continuous_of_smooth (data.scalarSmooth vector point)
  have matrixContinuity : Continuous (fun parameter : Parameter => fun _ : Fin 1 => rotation parameter) :=
    continuous_pi (fun _ => rotation_continuous)
  exact smoothContinuity.comp matrixContinuity

noncomputable def scalarOrbit (data : CuspidalRepresentation) (point : BinaryAdelicGL) :
    data.smooth →ₗ[ℂ] C(Parameter, ℂ) where
  toFun vector := ⟨fun parameter => data.realize vector (point * atInfinity (rotation parameter)),
    scalarOrbit_continuous data point vector⟩
  map_add' first second := by
    ext parameter
    exact congrFun (data.realize.map_add first second) _
  map_smul' scalar vector := by
    ext parameter
    exact congrFun (data.realize.map_smul scalar vector) _

noncomputable def scalarCoefficient (data : CuspidalRepresentation) (point : BinaryAdelicGL) (index : ℤ) :
    data.smooth →ₗ[ℂ] ℂ := (coefficientOperator index).toLinearMap.comp (scalarOrbit data point)

theorem scalarCoefficient_translate (data : CuspidalRepresentation) (point : BinaryAdelicGL)
    (index : ℤ) (parameter : Parameter) (vector : data.smooth) :
    scalarCoefficient data point index
      ⟨data.π (atInfinity (rotation parameter)) vector.val, data.smooth_stable _ _ vector.property⟩ =
        fourier index parameter * scalarCoefficient data point index vector := by
  have equality :
      (fun time : Parameter => data.realize
        ⟨data.π (atInfinity (rotation parameter)) vector.val, data.smooth_stable _ _ vector.property⟩
        (point * atInfinity (rotation time))) =
      (fun time : Parameter => scalarOrbit data point vector (parameter + time)) := by
    funext time
    change data.realize
      ⟨data.π (atInfinity (rotation parameter)) vector.val, data.smooth_stable _ _ vector.property⟩
      (point * atInfinity (rotation time)) =
        data.realize vector (point * atInfinity (rotation (parameter + time)))
    rw [data.equivariant, mul_assoc, ← TernaryPeriodPolynomials.PlaneEisensteinContinuation.Height.atInfinity_mul, ← rotation_add, add_comm time parameter]
  change fourierCoeff
      (fun time : Parameter => data.realize
        ⟨data.π (atInfinity (rotation parameter)) vector.val, data.smooth_stable _ _ vector.property⟩
        (point * atInfinity (rotation time))) index = _
  rw [equality, fourierCoeff_translate]
  rfl

theorem scalarCoefficient_smoothMode (data : CuspidalRepresentation) (point : BinaryAdelicGL)
    (index : ℤ) (vector : data.smooth) :
    scalarCoefficient data point index (smoothMode data index vector) =
      data.realize (smoothMode data index vector) point := by
  have equality : scalarOrbit data point (smoothMode data index vector) =
      data.realize (smoothMode data index vector) point • fourier index := by
    ext parameter
    change data.realize (smoothMode data index vector) (point * atInfinity (rotation parameter)) =
      data.realize (smoothMode data index vector) point * fourier index parameter
    rw [smoothMode_realize_eigen, mul_comm]
  change coefficientOperator index (scalarOrbit data point (smoothMode data index vector)) = _
  rw [equality, map_smul, coefficientOperator_apply, fourierCoeff_fourier]
  simp

/-- An algebraic rotation difference solution is enough to commute realization with one Fourier projection. -/
theorem scalarCoefficient_eq_mode_of_difference (data : CuspidalRepresentation) (point : BinaryAdelicGL)
    (index : ℤ) (parameter : Parameter) (vector solution : data.smooth)
    (identity : data.π (atInfinity (rotation parameter)) solution.val - fourier index parameter • solution.val =
      vector.val - (smoothMode data index vector).val) :
    scalarCoefficient data point index vector = data.realize (smoothMode data index vector) point := by
  have smoothIdentity :
      (⟨data.π (atInfinity (rotation parameter)) solution.val,
        data.smooth_stable _ _ solution.property⟩ : data.smooth) - fourier index parameter • solution =
      vector - smoothMode data index vector := Subtype.ext identity
  have coefficientIdentity := congrArg (scalarCoefficient data point index) smoothIdentity
  rw [map_sub, map_sub, map_smul, scalarCoefficient_translate, scalarCoefficient_smoothMode] at coefficientIdentity
  change fourier index parameter * scalarCoefficient data point index solution -
      fourier index parameter * scalarCoefficient data point index solution =
    scalarCoefficient data point index vector - data.realize (smoothMode data index vector) point at coefficientIdentity
  rw [sub_self] at coefficientIdentity
  exact sub_eq_zero.mp coefficientIdentity.symm

theorem scalarCoefficient_eq_mode_of_multiplier (data : CuspidalRepresentation) (point : BinaryAdelicGL)
    (index : ℤ) (order : ℕ) (kernel : C(Parameter, ℂ)) (parameter : Parameter)
    (multiplier : ∀ frequencyIndex : ℤ, frequencyIndex ≠ index →
      (fourier frequencyIndex parameter - fourier index parameter) * fourierCoeff kernel (-frequencyIndex) *
        (frequency frequencyIndex - frequency index) ^ order = 1)
    (vector : data.smooth) :
    scalarCoefficient data point index vector = data.realize (smoothMode data index vector) point :=
  scalarCoefficient_eq_mode_of_difference data point index parameter vector
    (differenceSolution data index order kernel vector)
    (differenceSolution_identity data index order kernel parameter multiplier vector)

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.RotationRealization
