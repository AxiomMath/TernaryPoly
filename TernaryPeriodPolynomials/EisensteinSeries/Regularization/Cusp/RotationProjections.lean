module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Cusp.RotationFourier

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

theorem circle_fourier_inverse_product (weight : ℤ) (angle : AddCircle (1 : ℝ)) :
    fourier weight angle * fourier (-weight) angle = 1 := by
  rw [← fourier_add]
  simp

theorem cuspRotationProjection_rotation (cusp : CuspidalRepresentation) (weight : ℤ)
    (vector : cusp.H) (angle : AddCircle (1 : ℝ)) :
    cuspCircularOrbit cusp (cuspRotationProjection cusp weight vector) angle =
      fourier weight angle • cuspRotationProjection cusp weight vector := by
  let action := (cuspUnitaryAction cusp (atInfinity (binaryCircleRotation angle.toCircle))).toContinuousLinearMap
  change action (∫ parameter : AddCircle (1 : ℝ),
      fourier (-weight) parameter • cuspCircularOrbit cusp vector parameter ∂AddCircle.haarAddCircle) =
    fourier weight angle • ∫ parameter : AddCircle (1 : ℝ),
      fourier (-weight) parameter • cuspCircularOrbit cusp vector parameter ∂AddCircle.haarAddCircle
  rw [← action.integral_comp_comm (cuspRotationFourier_integrable cusp weight vector)]
  calc
    _ = ∫ parameter : AddCircle (1 : ℝ), fourier weight angle •
        (fourier (-weight) (angle + parameter) • cuspCircularOrbit cusp vector (angle + parameter)) ∂AddCircle.haarAddCircle := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro parameter
      dsimp only
      rw [map_smul action]
      change fourier (-weight) parameter • cuspCircularOrbit cusp (cuspCircularOrbit cusp vector parameter) angle = _
      rw [← cuspCircularOrbit_add, circle_fourier_add, smul_smul, ← mul_assoc,
        circle_fourier_inverse_product, one_mul]
    _ = _ := by
      rw [integral_smul, integral_add_left_eq_self
        (fun parameter : AddCircle (1 : ℝ) => fourier (-weight) parameter • cuspCircularOrbit cusp vector parameter) angle]

theorem circle_fourier_integral_product (first second : ℤ) :
    (∫ angle : AddCircle (1 : ℝ), fourier (-second) angle * fourier first angle ∂AddCircle.haarAddCircle) =
      if first = second then 1 else 0 := by
  have coefficients := congrFun (fourierCoeff_fourier (T := (1 : ℝ)) first) second
  simpa [fourierCoeff, Pi.single_apply, eq_comm] using coefficients

theorem cuspRotationProjection_of_character (cusp : CuspidalRepresentation) (weight projectedWeight : ℤ)
    (vector : cusp.H)
    (character : ∀ angle : AddCircle (1 : ℝ), cuspCircularOrbit cusp vector angle = fourier weight angle • vector) :
    cuspRotationProjection cusp projectedWeight vector = if weight = projectedWeight then vector else 0 := by
  change (∫ angle : AddCircle (1 : ℝ), fourier (-projectedWeight) angle • cuspCircularOrbit cusp vector angle
    ∂AddCircle.haarAddCircle) = _
  simp only [character, smul_smul, integral_smul_const, circle_fourier_integral_product]
  split_ifs <;> simp

theorem cuspRotationProjection_idempotent (cusp : CuspidalRepresentation) (weight : ℤ) (vector : cusp.H) :
    cuspRotationProjection cusp weight (cuspRotationProjection cusp weight vector) = cuspRotationProjection cusp weight vector := by
  simpa only [ite_true] using cuspRotationProjection_of_character cusp weight weight
    (cuspRotationProjection cusp weight vector) (cuspRotationProjection_rotation cusp weight vector)

theorem cuspRotationProjection_distinct (cusp : CuspidalRepresentation) (first second : ℤ) (distinct : first ≠ second)
    (vector : cusp.H) :
    cuspRotationProjection cusp second (cuspRotationProjection cusp first vector) = 0 := by
  simpa only [ite_eq_right distinct] using cuspRotationProjection_of_character cusp first second
    (cuspRotationProjection cusp first vector) (cuspRotationProjection_rotation cusp first vector)

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
