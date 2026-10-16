module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Cusp.WeightLadder

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

theorem cuspRotationProjection_inner_projected (cusp : CuspidalRepresentation) (weight : ℤ)
    (first second : cusp.H) :
    inner ℂ (cuspRotationProjection cusp weight first) (cuspRotationProjection cusp weight second) =
      inner ℂ (cuspRotationProjection cusp weight first) second := by
  change inner ℂ (cuspRotationProjection cusp weight first)
    (∫ angle : AddCircle (1 : ℝ), fourier (-weight) angle • cuspCircularOrbit cusp second angle
      ∂AddCircle.haarAddCircle) = _
  rw [← integral_inner (𝕜 := ℂ) (cuspRotationFourier_integrable cusp weight second)]
  have integrand (angle : AddCircle (1 : ℝ)) :
      inner ℂ (cuspRotationProjection cusp weight first) (fourier (-weight) angle • cuspCircularOrbit cusp second angle) =
        inner ℂ (cuspRotationProjection cusp weight first) second := by
    have unitary := (cuspUnitaryAction cusp (atInfinity (binaryCircleRotation angle.toCircle))).inner_map_map
      (cuspRotationProjection cusp weight first) second
    change inner ℂ (cuspCircularOrbit cusp (cuspRotationProjection cusp weight first) angle)
      (cuspCircularOrbit cusp second angle) = _ at unitary
    rw [cuspRotationProjection_rotation, inner_smul_left] at unitary
    simpa only [inner_smul_right, fourier_neg] using unitary
  simp only [integrand]
  simp

theorem cuspRotationProjection_self_adjoint (cusp : CuspidalRepresentation) (weight : ℤ)
    (first second : cusp.H) :
    inner ℂ (cuspRotationProjection cusp weight first) second =
      inner ℂ first (cuspRotationProjection cusp weight second) := by
  rw [← cuspRotationProjection_inner_projected cusp weight first second]
  have swapped := congrArg (starRingEnd ℂ) (cuspRotationProjection_inner_projected cusp weight second first)
  simpa only [inner_conj_symm] using swapped

theorem cuspSmoothRotationProjection_generator (cusp : CuspidalRepresentation) (weight : ℤ)
    (vector : cusp.smooth) :
    cuspSmoothRotationProjection cusp weight (cuspRotationOperator cusp vector) =
      (Complex.I * (weight : ℂ)) • cuspSmoothRotationProjection cusp weight vector := by
  apply ext_inner_left ℂ
  intro test
  change inner ℂ test.val (cuspRotationProjection cusp weight (cuspRotationOperator cusp vector).val) =
    inner ℂ test.val ((Complex.I * (weight : ℂ)) • cuspRotationProjection cusp weight vector.val)
  rw [inner_smul_right, ← cuspRotationProjection_self_adjoint, ← cuspRotationProjection_self_adjoint]
  have skew := cuspDerivedAction_skew cusp binaryRotationDirection
    (cuspSmoothRotationProjection cusp weight test) vector
  change inner ℂ (cuspRotationOperator cusp (cuspSmoothRotationProjection cusp weight test)).val vector.val +
    inner ℂ (cuspRotationProjection cusp weight test.val) (cuspRotationOperator cusp vector).val = 0 at skew
  rw [cuspSmoothRotationProjection_eigenvector, Submodule.coe_smul, inner_smul_left,
    map_mul, Complex.conj_I, map_intCast] at skew
  change (-Complex.I * (weight : ℂ)) * inner ℂ (cuspRotationProjection cusp weight test.val) vector.val + _ = 0 at skew
  linear_combination skew

theorem cuspSmoothRotationProjection_commutes_generator (cusp : CuspidalRepresentation) (weight : ℤ)
    (vector : cusp.smooth) :
    cuspSmoothRotationProjection cusp weight (cuspRotationOperator cusp vector) =
      cuspRotationOperator cusp (cuspSmoothRotationProjection cusp weight vector) := by
  rw [cuspSmoothRotationProjection_generator, cuspSmoothRotationProjection_eigenvector]

theorem cuspSmoothRotationProjection_generator_pow (cusp : CuspidalRepresentation) (weight : ℤ)
    (order : ℕ) (vector : cusp.smooth) :
    cuspSmoothRotationProjection cusp weight ((cuspRotationOperator cusp ^ order) vector) =
      (Complex.I * (weight : ℂ)) ^ order • cuspSmoothRotationProjection cusp weight vector := by
  induction order with
  | zero => simp
  | succ order induction =>
    rw [pow_succ', Module.End.mul_apply, cuspSmoothRotationProjection_generator, induction, smul_smul, pow_succ']

theorem cuspRotationProjection_weighted_norm_le (cusp : CuspidalRepresentation) (weight : ℤ)
    (order : ℕ) (vector : cusp.smooth) :
    |(weight : ℝ)| ^ order * ‖cuspRotationProjection cusp weight vector.val‖ ≤
      ‖((cuspRotationOperator cusp ^ order) vector).val‖ := by
  have projection := congrArg (fun smoothVector : cusp.smooth => ‖smoothVector.val‖)
    (cuspSmoothRotationProjection_generator_pow cusp weight order vector)
  simp only [cuspSmoothRotationProjection_apply_val, Submodule.coe_smul, norm_smul,
    norm_pow, norm_mul, Complex.norm_I, one_mul, Complex.norm_intCast] at projection
  rw [← projection]
  exact cuspRotationFourier_norm_le cusp weight ((cuspRotationOperator cusp ^ order) vector).val

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
