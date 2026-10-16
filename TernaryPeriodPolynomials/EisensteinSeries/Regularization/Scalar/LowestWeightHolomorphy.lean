module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Scalar.UpperHalfCoordinates

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

theorem cohomological_upperHalfOrbit_cauchyRiemann {cusp : CuspidalRepresentation} {degree : ℕ}
    (cohomological : Cohomological cusp degree) (weight : ℝ) (vector : cusp.smooth)
    (rotation : cuspRotationOperator cusp vector = (Complex.I * (weight : ℂ)) • vector)
    (lowering : cuspLoweringOperator cusp vector = 0)
    (argument : BinaryAdelicGL) (point : ℂ) (positive : 0 < point.im) :
    fderiv ℝ (cuspUpperHalfOrbit cusp vector argument) point Complex.I =
      Complex.I * fderiv ℝ (cuspUpperHalfOrbit cusp vector argument) point 1 +
        ((weight / (2 * point.im) : ℝ) : ℂ) * cuspUpperHalfOrbit cusp vector argument point := by
  have split : cuspSplitOperator cusp vector = Complex.I • cuspSymmetricOperator cusp vector := by
    exact sub_eq_zero.mp lowering
  rw [cohomological_upperHalfOrbit_fderiv_imaginary cohomological vector argument point positive,
    cuspUpperHalfOrbit_fderiv_real cusp vector argument point positive, split, rotation]
  simp only [cuspUpperHalfOrbit_apply, map_smul, Pi.smul_apply, Complex.real_smul, smul_eq_mul,
    Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_inv, div_eq_mul_inv]
  ring_nf
  simp [Complex.I_sq]

noncomputable def cuspHolomorphicFunction (cusp : CuspidalRepresentation) (weight : ℝ)
    (vector : cusp.smooth) (argument : BinaryAdelicGL) (point : ℂ) : ℂ :=
  (point.im ^ (-weight / 2) : ℝ) • cuspUpperHalfOrbit cusp vector argument point

theorem cuspHolomorphicFunction_hasFDerivAt_real (cusp : CuspidalRepresentation) (weight : ℝ)
    (vector : cusp.smooth) (argument : BinaryAdelicGL) (point : ℂ) (positive : 0 < point.im) :
    HasFDerivAt (cuspHolomorphicFunction cusp weight vector argument)
      ((point.im ^ (-weight / 2) : ℝ) • fderiv ℝ (cuspUpperHalfOrbit cusp vector argument) point +
        ((-weight / 2 * point.im ^ (-weight / 2 - 1)) • Complex.imCLM).smulRight
          (cuspUpperHalfOrbit cusp vector argument point)) point := by
  have power := (Complex.imCLM.hasFDerivAt (x := point)).rpow_const
    (p := -weight / 2) (Or.inl positive.ne')
  exact power.smul (cuspUpperHalfOrbit_hasFDerivAt cusp vector argument point positive).differentiableAt.hasFDerivAt

theorem cohomological_holomorphicFunction_cauchyRiemann {cusp : CuspidalRepresentation} {degree : ℕ}
    (cohomological : Cohomological cusp degree) (weight : ℝ) (vector : cusp.smooth)
    (rotation : cuspRotationOperator cusp vector = (Complex.I * (weight : ℂ)) • vector)
    (lowering : cuspLoweringOperator cusp vector = 0)
    (argument : BinaryAdelicGL) (point : ℂ) (positive : 0 < point.im) :
    fderiv ℝ (cuspHolomorphicFunction cusp weight vector argument) point Complex.I =
      Complex.I • fderiv ℝ (cuspHolomorphicFunction cusp weight vector argument) point 1 := by
  rw [(cuspHolomorphicFunction_hasFDerivAt_real cusp weight vector argument point positive).fderiv]
  simp only [_root_.add_apply, _root_.smul_apply,
    ContinuousLinearMap.smulRight_apply, Complex.imCLM_apply, Complex.I_im, Complex.one_im,
    smul_eq_mul, mul_one, mul_zero, zero_smul, add_zero]
  rw [cohomological_upperHalfOrbit_cauchyRiemann cohomological weight vector rotation lowering argument point positive,
    Real.rpow_sub_one positive.ne']
  simp only [Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_neg,
    Complex.ofReal_ofNat]
  ring

theorem cohomological_holomorphicFunction_differentiableAt {cusp : CuspidalRepresentation} {degree : ℕ}
    (cohomological : Cohomological cusp degree) (weight : ℝ) (vector : cusp.smooth)
    (rotation : cuspRotationOperator cusp vector = (Complex.I * (weight : ℂ)) • vector)
    (lowering : cuspLoweringOperator cusp vector = 0)
    (argument : BinaryAdelicGL) (point : ℂ) (positive : 0 < point.im) :
    DifferentiableAt ℂ (cuspHolomorphicFunction cusp weight vector argument) point := by
  have real_derivative :=
    (cuspHolomorphicFunction_hasFDerivAt_real cusp weight vector argument point positive).differentiableAt.hasFDerivAt
  exact (real_derivative.complexOfReal_hasFDerivAt
    (cohomological_holomorphicFunction_cauchyRiemann cohomological weight vector rotation lowering argument point positive)).differentiableAt

theorem cohomological_holomorphicFunction_analyticOnNhd {cusp : CuspidalRepresentation} {degree : ℕ}
    (cohomological : Cohomological cusp degree) (weight : ℝ) (vector : cusp.smooth)
    (rotation : cuspRotationOperator cusp vector = (Complex.I * (weight : ℂ)) • vector)
    (lowering : cuspLoweringOperator cusp vector = 0) (argument : BinaryAdelicGL) :
    AnalyticOnNhd ℂ (cuspHolomorphicFunction cusp weight vector argument) {point | 0 < point.im} := by
  have differentiable : DifferentiableOn ℂ (cuspHolomorphicFunction cusp weight vector argument)
      {point | 0 < point.im} := fun point positive =>
    (cohomological_holomorphicFunction_differentiableAt cohomological weight vector rotation lowering argument point positive).differentiableWithinAt
  exact differentiable.analyticOnNhd (isOpen_lt continuous_const Complex.continuous_im)

theorem cuspHolomorphicFunction_norm_le (cusp : CuspidalRepresentation) (weight : ℝ)
    (vector : cusp.smooth) (argument : BinaryAdelicGL) (point : ℂ) (positive : 0 < point.im) :
    ‖cuspHolomorphicFunction cusp weight vector argument point‖ ≤
      point.im ^ (-weight / 2) * ‖cuspBoundedRealization cusp vector‖ := by
  rw [cuspHolomorphicFunction, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg positive.le _), cuspUpperHalfOrbit_apply]
  exact mul_le_mul_of_nonneg_left
    (BoundedContinuousFunction.norm_coe_le_norm (cuspBoundedRealization cusp vector) _)
    (Real.rpow_nonneg positive.le _)

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
