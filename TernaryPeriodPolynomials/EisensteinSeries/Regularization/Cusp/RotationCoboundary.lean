module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Cusp.RotationMultipliers

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

theorem cuspSmoothRotationProjection_ext (cusp : CuspidalRepresentation) {first second : cusp.smooth}
    (equal : ∀ weight, cuspSmoothRotationProjection cusp weight first = cuspSmoothRotationProjection cusp weight second) :
    first = second := by
  apply Subtype.ext
  apply sub_eq_zero.mp
  apply cuspRotationProjection_complete cusp
  intro weight
  rw [map_sub, sub_eq_zero]
  exact congrArg Subtype.val (equal weight)

theorem cuspSmoothRotationProjection_action (cusp : CuspidalRepresentation) (weight : ℤ)
    (angle : AddCircle (1 : ℝ)) (vector : cusp.smooth) :
    cuspSmoothRotationProjection cusp weight
      (cuspSmoothAction cusp (atInfinity (binaryCircleRotation angle.toCircle)) vector) =
        fourier weight angle • cuspSmoothRotationProjection cusp weight vector :=
  Subtype.ext (cuspRotationProjection_orbit cusp weight vector.val angle)

theorem cuspSmoothRotationProjection_projection (cusp : CuspidalRepresentation) (first second : ℤ)
    (vector : cusp.smooth) :
    cuspSmoothRotationProjection cusp first (cuspSmoothRotationProjection cusp second vector) =
      if second = first then cuspSmoothRotationProjection cusp second vector else 0 := by
  by_cases equal : second = first
  · subst second
    rw [ite_eq_left rfl]
    exact Subtype.ext (cuspRotationProjection_idempotent cusp first vector.val)
  · rw [ite_eq_right equal]
    exact Subtype.ext (cuspRotationProjection_distinct cusp second first equal vector.val)

noncomputable def cuspShiftedRotationOperator (cusp : CuspidalRepresentation) (shift : ℤ) : Module.End ℂ cusp.smooth :=
  cuspRotationOperator cusp - (Complex.I * (shift : ℂ)) • 1

theorem cuspShiftedRotationOperator_projection (cusp : CuspidalRepresentation) (shift weight : ℤ)
    (vector : cusp.smooth) :
    cuspSmoothRotationProjection cusp weight (cuspShiftedRotationOperator cusp shift vector) =
      (Complex.I * ((weight - shift : ℤ) : ℂ)) • cuspSmoothRotationProjection cusp weight vector := by
  simp only [cuspShiftedRotationOperator, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.one_apply, map_sub, map_smul, cuspSmoothRotationProjection_generator, Int.cast_sub]
  module

theorem cuspShiftedRotationOperator_pow_projection (cusp : CuspidalRepresentation) (shift weight : ℤ)
    (order : ℕ) (vector : cusp.smooth) :
    cuspSmoothRotationProjection cusp weight ((cuspShiftedRotationOperator cusp shift ^ order) vector) =
      (Complex.I * ((weight - shift : ℤ) : ℂ)) ^ order • cuspSmoothRotationProjection cusp weight vector := by
  induction order with
  | zero => simp
  | succ order induction =>
    rw [pow_succ', Module.End.mul_apply, cuspShiftedRotationOperator_projection, induction, smul_smul, pow_succ']

theorem cuspRotation_coboundary_of_kernel (cusp : CuspidalRepresentation) (weight : ℤ)
    (angle : AddCircle (1 : ℝ)) (order : ℕ) (kernel : C(AddCircle (1 : ℝ), ℂ))
    (coefficients : ∀ other : ℤ,
      (fourier other angle - fourier weight angle) * fourierCoeff kernel (-other) *
        (Complex.I * ((other - weight : ℤ) : ℂ)) ^ order = if other = weight then 0 else 1)
    (vector : cusp.smooth) :
    ∃ primitive : cusp.smooth,
      cuspSmoothAction cusp (atInfinity (binaryCircleRotation angle.toCircle)) primitive -
        fourier weight angle • primitive = vector - cuspSmoothRotationProjection cusp weight vector := by
  let primitive := cuspSmoothRotationAverage cusp kernel ((cuspShiftedRotationOperator cusp weight ^ order) vector)
  refine ⟨primitive, ?_⟩
  apply cuspSmoothRotationProjection_ext cusp
  intro other
  rw [map_sub, cuspSmoothRotationProjection_action, map_smul, ← sub_smul]
  change (fourier other angle - fourier weight angle) •
    cuspSmoothRotationProjection cusp other
      (cuspSmoothRotationAverage cusp kernel ((cuspShiftedRotationOperator cusp weight ^ order) vector)) = _
  rw [cuspSmoothRotationAverage_projection, cuspShiftedRotationOperator_pow_projection,
    smul_smul, smul_smul, coefficients, map_sub, cuspSmoothRotationProjection_projection]
  by_cases equal : other = weight
  · subst other
    simp
  · simp only [ite_eq_right equal, ite_eq_right (Ne.symm equal), one_smul, sub_zero]

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
