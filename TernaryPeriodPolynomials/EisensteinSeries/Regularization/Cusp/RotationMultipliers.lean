module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Cusp.RotationAverage

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

theorem cuspRotationProjection_orbit (cusp : CuspidalRepresentation) (weight : ℤ)
    (vector : cusp.H) (angle : AddCircle (1 : ℝ)) :
    cuspRotationProjection cusp weight (cuspCircularOrbit cusp vector angle) =
      fourier weight angle • cuspRotationProjection cusp weight vector := by
  calc
    _ = cuspCircularOrbit cusp (cuspRotationProjection cusp weight vector) angle := by
      let action := (cuspUnitaryAction cusp (atInfinity (binaryCircleRotation angle.toCircle))).toContinuousLinearMap
      change (∫ parameter : AddCircle (1 : ℝ), fourier (-weight) parameter •
        cuspCircularOrbit cusp (cuspCircularOrbit cusp vector angle) parameter ∂AddCircle.haarAddCircle) =
          action (∫ parameter : AddCircle (1 : ℝ), fourier (-weight) parameter •
            cuspCircularOrbit cusp vector parameter ∂AddCircle.haarAddCircle)
      rw [← action.integral_comp_comm (cuspRotationFourier_integrable cusp weight vector)]
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro parameter
      dsimp only
      rw [map_smul action]
      change fourier (-weight) parameter • cuspCircularOrbit cusp (cuspCircularOrbit cusp vector angle) parameter =
        fourier (-weight) parameter • cuspCircularOrbit cusp (cuspCircularOrbit cusp vector parameter) angle
      rw [← cuspCircularOrbit_add, ← cuspCircularOrbit_add, add_comm parameter angle]
    _ = _ := cuspRotationProjection_rotation cusp weight vector angle

theorem cuspRotationAverage_projection (cusp : CuspidalRepresentation)
    (kernel : C(AddCircle (1 : ℝ), ℂ)) (weight : ℤ) (vector : cusp.H) :
    cuspRotationProjection cusp weight (cuspRotationAverage cusp kernel vector) =
      fourierCoeff kernel (-weight) • cuspRotationProjection cusp weight vector := by
  rw [cuspRotationAverage_apply,
    ← (cuspRotationProjection cusp weight).integral_comp_comm (cuspRotationAverage_integrable cusp kernel vector)]
  calc
    _ = ∫ angle : AddCircle (1 : ℝ), (kernel angle * fourier weight angle) •
        cuspRotationProjection cusp weight vector ∂AddCircle.haarAddCircle := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro angle
      dsimp only
      rw [map_smul, cuspRotationProjection_orbit, smul_smul]
    _ = _ := by
      rw [integral_smul_const]
      congr 1
      simp only [fourierCoeff, neg_neg, smul_eq_mul, mul_comm]

noncomputable def cuspSmoothRotationAverage (cusp : CuspidalRepresentation)
    (kernel : C(AddCircle (1 : ℝ), ℂ)) : Module.End ℂ cusp.smooth :=
  ((cuspRotationAverage cusp kernel).toLinearMap.comp cusp.smooth.subtype).codRestrict cusp.smooth
    (cuspRotationAverage_mem_smooth cusp kernel)

theorem cuspSmoothRotationAverage_apply_val (cusp : CuspidalRepresentation)
    (kernel : C(AddCircle (1 : ℝ), ℂ)) (vector : cusp.smooth) :
    (cuspSmoothRotationAverage cusp kernel vector).val = cuspRotationAverage cusp kernel vector.val := rfl

theorem cuspSmoothRotationAverage_projection (cusp : CuspidalRepresentation)
    (kernel : C(AddCircle (1 : ℝ), ℂ)) (weight : ℤ) (vector : cusp.smooth) :
    cuspSmoothRotationProjection cusp weight (cuspSmoothRotationAverage cusp kernel vector) =
      fourierCoeff kernel (-weight) • cuspSmoothRotationProjection cusp weight vector :=
  Subtype.ext (cuspRotationAverage_projection cusp kernel weight vector.val)

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
