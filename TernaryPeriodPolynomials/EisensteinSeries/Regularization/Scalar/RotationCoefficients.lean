module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Cusp.RotationCoboundary

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

theorem circle_fourier_integrable (function : C(AddCircle (1 : ℝ), ℂ)) (weight : ℤ) :
    Integrable (fun angle => fourier (-weight) angle * function angle) AddCircle.haarAddCircle := by
  apply integrableOn_univ.mp
  exact ContinuousOn.integrableOn_compact isCompact_univ
    (((fourier (-weight)).continuous.mul function.continuous).continuousOn)

noncomputable def circleFourierCoefficientLinear (weight : ℤ) : C(AddCircle (1 : ℝ), ℂ) →ₗ[ℂ] ℂ where
  toFun function := fourierCoeff function weight
  map_add' first second := by
    change (∫ angle, fourier (-weight) angle * (first angle + second angle) ∂AddCircle.haarAddCircle) = _
    simp only [mul_add]
    exact integral_add (circle_fourier_integrable first weight) (circle_fourier_integrable second weight)
  map_smul' scalar function := by
    exact fourierCoeff.const_smul function scalar weight

theorem circle_fourier_translate (function : AddCircle (1 : ℝ) → ℂ) (weight : ℤ) (angle : AddCircle (1 : ℝ)) :
    fourierCoeff (fun parameter => function (parameter + angle)) weight =
      fourier weight angle * fourierCoeff function weight := by
  change (∫ parameter, fourier (-weight) parameter * function (parameter + angle) ∂AddCircle.haarAddCircle) = _
  calc
    _ = ∫ parameter : AddCircle (1 : ℝ), fourier weight angle *
        (fourier (-weight) (angle + parameter) * function (angle + parameter)) ∂AddCircle.haarAddCircle := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro parameter
      dsimp only
      rw [circle_fourier_add]
      calc
        _ = (fourier weight angle * fourier (-weight) angle) *
            (fourier (-weight) parameter * function (angle + parameter)) := by
          rw [circle_fourier_inverse_product, one_mul, add_comm parameter angle]
        _ = _ := by ring
    _ = _ := by
      rw [integral_const_mul, integral_add_left_eq_self
        (fun parameter : AddCircle (1 : ℝ) => fourier (-weight) parameter * function parameter) angle]
      rfl

noncomputable def cuspScalarCircleOrbit (cusp : CuspidalRepresentation) (argument : BinaryAdelicGL) :
    cusp.smooth →ₗ[ℂ] C(AddCircle (1 : ℝ), ℂ) where
  toFun vector :=
    { toFun := fun angle => cusp.realize vector (argument * atInfinity (binaryCircleRotation angle.toCircle))
      continuous_toFun := (cusp_realize_continuous cusp vector).comp
        (continuous_const.mul (binary_atInfinity_continuous.comp
          (binaryCircleRotation_continuous.comp AddCircle.continuous_toCircle))) }
  map_add' first second := by
    ext angle
    exact congrFun (map_add cusp.realize first second) _
  map_smul' scalar vector := by
    ext angle
    exact congrFun (map_smul cusp.realize scalar vector) _

theorem cuspScalarCircleOrbit_apply (cusp : CuspidalRepresentation) (argument : BinaryAdelicGL)
    (vector : cusp.smooth) (angle : AddCircle (1 : ℝ)) :
    cuspScalarCircleOrbit cusp argument vector angle =
      cusp.realize vector (argument * atInfinity (binaryCircleRotation angle.toCircle)) := rfl

theorem cuspScalarCircleOrbit_action (cusp : CuspidalRepresentation) (argument : BinaryAdelicGL)
    (vector : cusp.smooth) (angle parameter : AddCircle (1 : ℝ)) :
    cuspScalarCircleOrbit cusp argument
      (cuspSmoothAction cusp (atInfinity (binaryCircleRotation angle.toCircle)) vector) parameter =
        cuspScalarCircleOrbit cusp argument vector (parameter + angle) := by
  have equivariant := cusp.equivariant (atInfinity (binaryCircleRotation angle.toCircle)) vector
    (argument * atInfinity (binaryCircleRotation parameter.toCircle))
  change cusp.realize (cuspSmoothAction cusp (atInfinity (binaryCircleRotation angle.toCircle)) vector)
    (argument * atInfinity (binaryCircleRotation parameter.toCircle)) = _ at equivariant
  rw [cuspScalarCircleOrbit_apply, equivariant, cuspScalarCircleOrbit_apply]
  rw [AddCircle.toCircle_add, map_mul, binary_atInfinity_mul, mul_assoc]

noncomputable def cuspScalarRotationCoefficient (cusp : CuspidalRepresentation) (argument : BinaryAdelicGL)
    (weight : ℤ) : cusp.smooth →ₗ[ℂ] ℂ :=
  (circleFourierCoefficientLinear weight).comp (cuspScalarCircleOrbit cusp argument)

theorem cuspScalarRotationCoefficient_apply (cusp : CuspidalRepresentation) (argument : BinaryAdelicGL)
    (weight : ℤ) (vector : cusp.smooth) :
    cuspScalarRotationCoefficient cusp argument weight vector =
      fourierCoeff (cuspScalarCircleOrbit cusp argument vector) weight := rfl

theorem cuspScalarRotationCoefficient_action (cusp : CuspidalRepresentation) (argument : BinaryAdelicGL)
    (weight : ℤ) (vector : cusp.smooth) (angle : AddCircle (1 : ℝ)) :
    cuspScalarRotationCoefficient cusp argument weight
      (cuspSmoothAction cusp (atInfinity (binaryCircleRotation angle.toCircle)) vector) =
        fourier weight angle * cuspScalarRotationCoefficient cusp argument weight vector := by
  change fourierCoeff (fun parameter => cuspScalarCircleOrbit cusp argument
    (cuspSmoothAction cusp (atInfinity (binaryCircleRotation angle.toCircle)) vector) parameter) weight = _
  simp only [cuspScalarCircleOrbit_action]
  exact circle_fourier_translate (cuspScalarCircleOrbit cusp argument vector) weight angle

theorem cuspScalarRotationCoefficient_projection (cusp : CuspidalRepresentation) (argument : BinaryAdelicGL)
    (weight : ℤ) (vector : cusp.smooth) :
    cuspScalarRotationCoefficient cusp argument weight (cuspSmoothRotationProjection cusp weight vector) =
      cusp.realize (cuspSmoothRotationProjection cusp weight vector) argument := by
  let projected := cuspSmoothRotationProjection cusp weight vector
  change (∫ angle : AddCircle (1 : ℝ), fourier (-weight) angle *
    cusp.realize projected (argument * atInfinity (binaryCircleRotation angle.toCircle)) ∂AddCircle.haarAddCircle) = _
  have character := cusp_realize_circle_character cusp weight projected
    (cuspSmoothRotationProjection_eigenvector cusp weight vector)
  simp only [character, ← mul_assoc]
  have inverse (angle : AddCircle (1 : ℝ)) : fourier (-weight) angle * fourier weight angle = 1 := by
    simpa only [neg_neg] using circle_fourier_inverse_product (-weight) angle
  simp only [inverse, one_mul]
  simp [projected]

theorem cusp_realize_projection_of_coboundary (cusp : CuspidalRepresentation) (argument : BinaryAdelicGL)
    (weight : ℤ) (angle : AddCircle (1 : ℝ)) (vector : cusp.smooth)
    (coboundary : ∃ primitive : cusp.smooth,
      cuspSmoothAction cusp (atInfinity (binaryCircleRotation angle.toCircle)) primitive -
        fourier weight angle • primitive = vector - cuspSmoothRotationProjection cusp weight vector) :
    cusp.realize (cuspSmoothRotationProjection cusp weight vector) argument =
      fourierCoeff (cuspScalarCircleOrbit cusp argument vector) weight := by
  obtain ⟨primitive, identity⟩ := coboundary
  have projected := congrArg (cuspScalarRotationCoefficient cusp argument weight) identity
  rw [map_sub, cuspScalarRotationCoefficient_action, map_smul, smul_eq_mul, sub_self,
    map_sub, cuspScalarRotationCoefficient_projection] at projected
  exact (sub_eq_zero.mp projected.symm).symm

theorem cusp_realize_projection_of_kernel (cusp : CuspidalRepresentation) (argument : BinaryAdelicGL)
    (weight : ℤ) (angle : AddCircle (1 : ℝ)) (order : ℕ) (kernel : C(AddCircle (1 : ℝ), ℂ))
    (coefficients : ∀ other : ℤ,
      (fourier other angle - fourier weight angle) * fourierCoeff kernel (-other) *
        (Complex.I * ((other - weight : ℤ) : ℂ)) ^ order = if other = weight then 0 else 1)
    (vector : cusp.smooth) :
    cusp.realize (cuspSmoothRotationProjection cusp weight vector) argument =
      fourierCoeff (cuspScalarCircleOrbit cusp argument vector) weight :=
  cusp_realize_projection_of_coboundary cusp argument weight angle vector
    (cuspRotation_coboundary_of_kernel cusp weight angle order kernel coefficients vector)

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
