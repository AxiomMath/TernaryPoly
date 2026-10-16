module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Cohomological.WeightSpectrum

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

theorem scalar_ode_exp_smul {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (function : ℝ → H) (scalar : ℂ)
    (derivative : ∀ point, HasDerivAt function (scalar • function point) point) (point : ℝ) :
    function point = Complex.exp (scalar * (point : ℂ)) • function 0 := by
  have weighted_derivative (parameter : ℝ) :
      HasDerivAt (fun real : ℝ => Complex.exp (-scalar * (real : ℂ)) • function real) 0 parameter := by
    have coefficient := (((hasDerivAt_id parameter).ofReal_comp).const_mul (-scalar)).cexp
    have product := coefficient.smul (derivative parameter)
    convert! product using 1
    simp only [id_eq, Complex.ofReal_one, mul_one, smul_smul, ← add_smul]
    have zero : Complex.exp (-scalar * (parameter : ℂ)) * scalar +
        Complex.exp (-scalar * (parameter : ℂ)) * -scalar = 0 := by ring
    rw [zero, zero_smul]
  have constant := is_const_of_deriv_eq_zero (fun parameter => (weighted_derivative parameter).differentiableAt)
    (fun parameter => (weighted_derivative parameter).deriv) point 0
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_smul] at constant
  have cancel : Complex.exp (scalar * (point : ℂ)) * Complex.exp (-scalar * (point : ℂ)) = 1 := by
    rw [← Complex.exp_add]
    have zero : scalar * (point : ℂ) + -scalar * (point : ℂ) = 0 := by ring
    rw [zero, Complex.exp_zero]
  calc
    _ = Complex.exp (scalar * (point : ℂ)) •
        (Complex.exp (-scalar * (point : ℂ)) • function point) := by rw [smul_smul, cancel, one_smul]
    _ = _ := by rw [constant]

theorem cuspRotationOrbit_hasDerivAt (cusp : CuspidalRepresentation) (vector : cusp.smooth) (point : ℝ) :
    HasDerivAt (fun parameter => cusp.π (atInfinity (binaryRotationPath parameter)) vector.val)
      (cusp.π (atInfinity (binaryRotationPath point)) (cuspRotationOperator cusp vector).val) point := by
  have initial := cuspSmoothAction_path_hasDerivAt cusp vector binaryRotationPath binaryRotationDirection 0
    binaryRotationPath_zero binaryRotationPath_entry_hasDerivAt_zero
  have at_zero : HasDerivAt (fun parameter => cusp.π (atInfinity (binaryRotationPath parameter)) vector.val)
      (cuspRotationOperator cusp vector).val (point - point) := by
    simpa only [sub_self, cuspSmoothAction_apply_val, cuspRotationOperator] using initial
  have shifted := at_zero.comp_sub_const point point
  let action := (cuspRealUnitaryAction cusp (atInfinity (binaryRotationPath point))).toContinuousLinearMap
  have translated := action.hasFDerivAt.comp_hasDerivAt point shifted
  apply translated.congr_of_eventuallyEq
  apply Filter.Eventually.of_forall
  intro parameter
  change cusp.π (atInfinity (binaryRotationPath parameter)) vector.val =
    cusp.π (atInfinity (binaryRotationPath point))
      (cusp.π (atInfinity (binaryRotationPath (parameter - point))) vector.val)
  rw [← Module.End.mul_apply, ← map_mul, ← binary_atInfinity_mul, ← binaryRotationPath_add]
  rw [show point + (parameter - point) = parameter by ring]

theorem cuspRotation_real_character_of_eigenvector (cusp : CuspidalRepresentation) (weight : ℂ)
    (vector : cusp.smooth)
    (rotation : cuspRotationOperator cusp vector = (Complex.I * weight) • vector) (parameter : ℝ) :
    cusp.π (atInfinity (binaryRotationPath parameter)) vector.val =
      Complex.exp (Complex.I * weight * (parameter : ℂ)) • vector.val := by
  have derivative (point : ℝ) := cuspRotationOrbit_hasDerivAt cusp vector point
  simp only [rotation, Submodule.coe_smul, map_smul] at derivative
  have value := scalar_ode_exp_smul
    (fun parameter => cusp.π (atInfinity (binaryRotationPath parameter)) vector.val)
    (Complex.I * weight) derivative parameter
  simpa only [binaryRotationPath_zero, binary_atInfinity_one, map_one, Module.End.one_apply] using value

theorem cuspRotation_circle_character_of_eigenvector (cusp : CuspidalRepresentation) (weight : ℤ)
    (vector : cusp.smooth)
    (rotation : cuspRotationOperator cusp vector = (Complex.I * (weight : ℂ)) • vector)
    (angle : AddCircle (1 : ℝ)) :
    cuspCircularOrbit cusp vector.val angle = fourier weight angle • vector.val := by
  induction angle using QuotientAddGroup.induction_on with
  | H angle =>
    have value := cuspRotation_real_character_of_eigenvector cusp weight vector rotation (2 * Real.pi * angle)
    simp only [cuspCircularOrbit, AddCircle.toCircle_apply_mk, div_one, fourier_coe_apply]
    convert! value using 1
    congr 2
    push_cast
    ring

theorem cuspRotationProjection_of_eigenvector (cusp : CuspidalRepresentation) (weight projectedWeight : ℤ)
    (vector : cusp.smooth)
    (rotation : cuspRotationOperator cusp vector = (Complex.I * (weight : ℂ)) • vector) :
    cuspRotationProjection cusp projectedWeight vector.val = if weight = projectedWeight then vector.val else 0 :=
  cuspRotationProjection_of_character cusp weight projectedWeight vector.val
    (cuspRotation_circle_character_of_eigenvector cusp weight vector rotation)

theorem cusp_realize_rotation_character (cusp : CuspidalRepresentation) (weight : ℂ)
    (vector : cusp.smooth)
    (rotation : cuspRotationOperator cusp vector = (Complex.I * weight) • vector)
    (parameter : ℝ) (argument : BinaryAdelicGL) :
    cusp.realize vector (argument * atInfinity (binaryRotationPath parameter)) =
      Complex.exp (Complex.I * weight * (parameter : ℂ)) * cusp.realize vector argument := by
  have action : cuspSmoothAction cusp (atInfinity (binaryRotationPath parameter)) vector =
      Complex.exp (Complex.I * weight * (parameter : ℂ)) • vector :=
    Subtype.ext (cuspRotation_real_character_of_eigenvector cusp weight vector rotation parameter)
  have equivariant := cusp.equivariant (atInfinity (binaryRotationPath parameter)) vector argument
  change cusp.realize (cuspSmoothAction cusp (atInfinity (binaryRotationPath parameter)) vector) argument = _ at equivariant
  rw [action, map_smul, Pi.smul_apply, smul_eq_mul] at equivariant
  exact equivariant.symm

theorem cusp_realize_circle_character (cusp : CuspidalRepresentation) (weight : ℤ)
    (vector : cusp.smooth)
    (rotation : cuspRotationOperator cusp vector = (Complex.I * (weight : ℂ)) • vector)
    (angle : AddCircle (1 : ℝ)) (argument : BinaryAdelicGL) :
    cusp.realize vector (argument * atInfinity (binaryCircleRotation angle.toCircle)) =
      fourier weight angle * cusp.realize vector argument := by
  have action : cuspSmoothAction cusp (atInfinity (binaryCircleRotation angle.toCircle)) vector =
      fourier weight angle • vector :=
    Subtype.ext (cuspRotation_circle_character_of_eigenvector cusp weight vector rotation angle)
  have equivariant := cusp.equivariant (atInfinity (binaryCircleRotation angle.toCircle)) vector argument
  change cusp.realize (cuspSmoothAction cusp (atInfinity (binaryCircleRotation angle.toCircle)) vector) argument = _ at equivariant
  rw [action, map_smul, Pi.smul_apply, smul_eq_mul] at equivariant
  exact equivariant.symm

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
