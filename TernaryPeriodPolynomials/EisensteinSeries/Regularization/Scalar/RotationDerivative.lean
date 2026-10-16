module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Scalar.RotationSeries

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

theorem rotation_exponential_norm (weight : ℤ) (parameter : ℝ) :
    ‖Complex.exp (Complex.I * (weight : ℂ) * (parameter : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  simp [Complex.mul_re, Complex.mul_im]

theorem cuspBoundedRealization_rotation_term_hasDerivAt (cusp : CuspidalRepresentation)
    (vector : cusp.smooth) (weight : ℤ) (parameter : ℝ) :
    HasDerivAt (fun point : ℝ => Complex.exp (Complex.I * (weight : ℂ) * (point : ℂ)) •
      cuspBoundedRealization cusp (cuspSmoothRotationProjection cusp weight vector))
      (Complex.exp (Complex.I * (weight : ℂ) * (parameter : ℂ)) •
        cuspBoundedRealization cusp (cuspSmoothRotationProjection cusp weight (cuspRotationOperator cusp vector)))
      parameter := by
  have coefficient := (((hasDerivAt_id parameter).ofReal_comp).const_mul (Complex.I * (weight : ℂ))).cexp
  have derivative := coefficient.smul_const (cuspBoundedRealization cusp (cuspSmoothRotationProjection cusp weight vector))
  simpa only [id_eq, Complex.ofReal_one, mul_one, cuspSmoothRotationProjection_generator, map_smul, smul_smul] using derivative

theorem cuspBoundedRealization_rotation_hasDerivAt (cusp : CuspidalRepresentation)
    (vector : cusp.smooth) (parameter : ℝ) :
    HasDerivAt (fun point => cuspBoundedRealization cusp
      (cuspSmoothAction cusp (atInfinity (binaryRotationPath point)) vector))
      (cuspBoundedRealization cusp
        (cuspSmoothAction cusp (atInfinity (binaryRotationPath parameter)) (cuspRotationOperator cusp vector)))
      parameter := by
  let terms := fun (weight : ℤ) (point : ℝ) => Complex.exp (Complex.I * (weight : ℂ) * (point : ℂ)) •
    cuspBoundedRealization cusp (cuspSmoothRotationProjection cusp weight vector)
  let derivatives := fun (weight : ℤ) (point : ℝ) => Complex.exp (Complex.I * (weight : ℂ) * (point : ℂ)) •
    cuspBoundedRealization cusp (cuspSmoothRotationProjection cusp weight (cuspRotationOperator cusp vector))
  have bounded (weight : ℤ) (point : ℝ) : ‖derivatives weight point‖ ≤
      ‖cuspBoundedRealization cusp (cuspSmoothRotationProjection cusp weight (cuspRotationOperator cusp vector))‖ := by
    simp only [derivatives, norm_smul, rotation_exponential_norm, one_mul, le_refl]
  have initial : Summable (fun weight => terms weight 0) := by
    simpa only [terms, Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_smul] using
      cuspBoundedRealization_projection_summable cusp vector
  have differentiated := hasDerivAt_tsum (g := terms) (g' := derivatives)
    (cuspBoundedRealization_projection_norm_summable cusp (cuspRotationOperator cusp vector))
    (cuspBoundedRealization_rotation_term_hasDerivAt cusp vector) bounded initial parameter
  simpa only [terms, derivatives, cuspBoundedRealization_rotation_tsum] using differentiated

theorem cuspBoundedRealization_rotation_hasDerivAt_zero (cusp : CuspidalRepresentation)
    (vector : cusp.smooth) :
    HasDerivAt (fun point => cuspBoundedRealization cusp
      (cuspSmoothAction cusp (atInfinity (binaryRotationPath point)) vector))
      (cuspBoundedRealization cusp (cuspRotationOperator cusp vector)) 0 := by
  simpa only [binaryRotationPath_zero, binary_atInfinity_one, map_one, Module.End.one_apply] using
    cuspBoundedRealization_rotation_hasDerivAt cusp vector 0

theorem cusp_realize_rotation_hasDerivAt (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (argument : BinaryAdelicGL) (parameter : ℝ) :
    HasDerivAt (fun point => cusp.realize vector (argument * atInfinity (binaryRotationPath point)))
      (cusp.realize (cuspRotationOperator cusp vector) (argument * atInfinity (binaryRotationPath parameter)))
      parameter := by
  let evaluation : BoundedContinuousFunction BinaryAdelicGL ℂ →L[ℝ] ℂ :=
    (BoundedContinuousFunction.evalCLM ℂ argument).restrictScalars ℝ
  have differentiated := evaluation.hasFDerivAt.comp_hasDerivAt parameter
    (cuspBoundedRealization_rotation_hasDerivAt cusp vector parameter)
  have evaluate (other : cusp.smooth) (point : ℝ) :
      evaluation (cuspBoundedRealization cusp (cuspSmoothAction cusp (atInfinity (binaryRotationPath point)) other)) =
        cusp.realize other (argument * atInfinity (binaryRotationPath point)) := cusp.equivariant _ _ _
  simpa only [Function.comp_def, evaluate] using differentiated

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
