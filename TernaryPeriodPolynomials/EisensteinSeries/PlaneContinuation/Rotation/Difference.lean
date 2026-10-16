module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Rotation.Convolution

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RotationCircle TernaryPeriodPolynomials.PlaneEisensteinContinuation.RotationFourier TernaryPeriodPolynomials.PlaneEisensteinContinuation.RotationDifferentiation
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RotationConvolution TernaryPeriodPolynomials.PlaneEisensteinContinuation.FourierDifferentiation

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.RotationDifference

noncomputable def shiftedDerivative (data : CuspidalRepresentation) (target : ℤ) : data.smooth →ₗ[ℂ] data.smooth :=
  rotationDerivative data - frequency target • LinearMap.id

theorem modeVector_shiftedDerivative (data : CuspidalRepresentation) (target index : ℤ) (vector : data.smooth) :
    modeVector data index (shiftedDerivative data target vector).val =
      (frequency index - frequency target) • modeVector data index vector.val := by
  change modeOperator data index ((rotationDerivative data vector).val - frequency target • vector.val) = _
  rw [map_sub, map_smul, modeOperator_apply, modeOperator_apply, modeVector_rotationDerivative, sub_smul]

theorem modeVector_iteratedShiftedDerivative (data : CuspidalRepresentation) (target index : ℤ)
    (vector : data.smooth) (order : ℕ) :
    modeVector data index ((shiftedDerivative data target ^ order) vector).val =
      (frequency index - frequency target) ^ order • modeVector data index vector.val := by
  induction order with
  | zero => simp
  | succ order inductionHypothesis =>
      rw [pow_succ', Module.End.mul_apply, modeVector_shiftedDerivative, inductionHypothesis,
        smul_smul, pow_succ']

noncomputable def differenceSolution (data : CuspidalRepresentation) (target : ℤ) (order : ℕ)
    (kernel : C(Parameter, ℂ)) (vector : data.smooth) : data.smooth :=
  smoothConvolution data kernel ((shiftedDerivative data target ^ order) vector)

/-- A scalar Fourier multiplier criterion gives an actual algebraic difference identity in the supplied smooth space. -/
theorem differenceSolution_identity (data : CuspidalRepresentation) (target : ℤ) (order : ℕ)
    (kernel : C(Parameter, ℂ)) (parameter : Parameter)
    (multiplier : ∀ index : ℤ, index ≠ target →
      (fourier index parameter - fourier target parameter) * fourierCoeff kernel (-index) *
        (frequency index - frequency target) ^ order = 1)
    (vector : data.smooth) :
    data.π (atInfinity (rotation parameter)) (differenceSolution data target order kernel vector).val -
      fourier target parameter • (differenceSolution data target order kernel vector).val =
        vector.val - (smoothMode data target vector).val := by
  apply eq_of_modes data
  intro index
  change modeOperator data index
      (data.π (atInfinity (rotation parameter)) (differenceSolution data target order kernel vector).val -
        fourier target parameter • (differenceSolution data target order kernel vector).val) =
    modeOperator data index (vector.val - modeVector data target vector.val)
  rw [map_sub, map_sub, map_smul, modeOperator_apply, modeOperator_apply, modeOperator_apply,
    modeOperator_apply, modeVector_translate, ← sub_smul, modeVector_comp]
  by_cases same : index = target
  · subst index
    simp
  · have modeSolution : modeVector data index (differenceSolution data target order kernel vector).val =
        fourierCoeff kernel (-index) • ((frequency index - frequency target) ^ order •
          modeVector data index vector.val) := by
      change modeVector data index (convolutionVector data kernel
        ((shiftedDerivative data target ^ order) vector).val) = _
      rw [modeVector_convolution, modeVector_iteratedShiftedDerivative]
    rw [modeSolution, smul_smul, smul_smul]
    rw [multiplier index same]
    simp [same]

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.RotationDifference
