module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Scalar.IntegralPeriodicity

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix Filter

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

theorem cuspUpperHalfOrbit_of_holomorphic (cusp : CuspidalRepresentation) (weight : ℝ)
    (vector : cusp.smooth) (argument : BinaryAdelicGL) (point : ℂ) (positive : 0 < point.im) :
    cuspUpperHalfOrbit cusp vector argument point =
      (point.im ^ (weight / 2) : ℝ) • cuspHolomorphicFunction cusp weight vector argument point := by
  rw [cuspHolomorphicFunction, smul_smul, ← Real.rpow_add positive]
  have exponents : weight / 2 + -weight / 2 = 0 := by ring
  rw [exponents, Real.rpow_zero, one_smul]

theorem binaryUpperHalfPoint_I : binaryUpperHalfPoint Complex.I = 1 := by
  apply Units.ext
  rw [binaryUpperHalfPoint_val _ (by norm_num)]
  ext row column
  fin_cases row <;> fin_cases column <;> simp [binaryUpperHalfMatrix]

theorem cuspHolomorphicFunction_I (cusp : CuspidalRepresentation) (weight : ℝ)
    (vector : cusp.smooth) (argument : BinaryAdelicGL) :
    cuspHolomorphicFunction cusp weight vector argument Complex.I = cusp.realize vector argument := by
  simp only [cuspHolomorphicFunction, Complex.I_im, Real.one_rpow, one_smul,
    cuspUpperHalfOrbit_apply, binaryUpperHalfPoint_I, binary_atInfinity_one, mul_one]

theorem cuspHolomorphicFunction_faithful (cusp : CuspidalRepresentation) (weight : ℝ)
    (first second : cusp.smooth)
    (equal : ∀ argument, cuspHolomorphicFunction cusp weight first argument Complex.I =
      cuspHolomorphicFunction cusp weight second argument Complex.I) : first = second := by
  apply cusp.injective
  funext argument
  simpa only [cuspHolomorphicFunction_I] using equal argument

theorem cohomological_principal_scalar_exp_decay {cusp : CuspidalRepresentation} {degree : ℕ}
    (cohomological : Cohomological cusp degree) (weight : ℝ) (weight_positive : 0 < weight)
    (vector : cuspFiniteFixedSubmodule cusp binaryPrincipalLevel)
    (rotation : cuspRotationOperator cusp vector.val = (Complex.I * (weight : ℂ)) • vector.val)
    (lowering : cuspLoweringOperator cusp vector.val = 0) :
    (fun point : UpperHalfPlane => cusp.realize vector.val (atInfinity (binaryUpperHalfPoint point)))
      =O[UpperHalfPlane.atImInfty] (fun point => Real.exp (-Real.pi * point.im / 3)) := by
  have height_tendsto : Tendsto UpperHalfPlane.im UpperHalfPlane.atImInfty atTop := tendsto_comap
  have power_bound := ((isLittleO_rpow_exp_pos_mul_atTop (weight / 2)
    (div_pos Real.pi_pos (by norm_num : (0 : ℝ) < 3))).isBigO).comp_tendsto height_tendsto
  have decay := cohomological_principal_lowest_exp_decay cohomological weight weight_positive vector rotation lowering
  have product := power_bound.smul decay
  apply product.congr
  · intro point
    change ((point : ℂ).im ^ (weight / 2) : ℝ) •
      cuspHolomorphicFunction cusp weight vector.val 1 point = _
    rw [← cuspUpperHalfOrbit_of_holomorphic cusp weight vector.val 1 point point.im_pos,
      cuspUpperHalfOrbit_apply, one_mul]
  · intro point
    change Real.exp (Real.pi / 3 * point.im) * Real.exp (-2 * Real.pi * point.im / 3) = _
    rw [← Real.exp_add]
    congr 1
    ring

theorem cohomological_principal_scalar_rapid_decay {cusp : CuspidalRepresentation} {degree : ℕ}
    (cohomological : Cohomological cusp degree) (weight : ℝ) (weight_positive : 0 < weight)
    (vector : cuspFiniteFixedSubmodule cusp binaryPrincipalLevel)
    (rotation : cuspRotationOperator cusp vector.val = (Complex.I * (weight : ℂ)) • vector.val)
    (lowering : cuspLoweringOperator cusp vector.val = 0) (exponent : ℝ) :
    (fun point : UpperHalfPlane => cusp.realize vector.val (atInfinity (binaryUpperHalfPoint point)))
      =o[UpperHalfPlane.atImInfty] (fun point => point.im ^ exponent) := by
  have height_tendsto : Tendsto UpperHalfPlane.im UpperHalfPlane.atImInfty atTop := tendsto_comap
  have exponential := (isLittleO_exp_neg_mul_rpow_atTop
    (div_pos Real.pi_pos (by norm_num : (0 : ℝ) < 3)) exponent).comp_tendsto height_tendsto
  have decay := cohomological_principal_scalar_exp_decay cohomological weight weight_positive vector rotation lowering
  apply decay.trans_isLittleO
  convert! exponential using 1
  funext point
  congr 1
  ring

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
