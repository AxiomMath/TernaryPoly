module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.ExponentialVectorBounds

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem real_exponential_weight_bound_scaled (weight lower upper argument radius : ℝ)
    (positive : 0 < radius) (lower_bound : lower ≤ argument) (upper_bound : argument ≤ upper) :
    Real.exp (argument * weight) * |weight| ≤
      (Real.exp ((lower - radius) * weight) + Real.exp ((upper + radius) * weight)) / radius := by
  have weight_bound : |weight| ≤ Real.exp (radius * |weight|) / radius := by
    apply (le_div_iff₀ positive).mpr
    linarith [Real.add_one_le_exp (radius * |weight|)]
  calc
    _ ≤ Real.exp (argument * weight) * (Real.exp (radius * |weight|) / radius) :=
      mul_le_mul_of_nonneg_left weight_bound (Real.exp_nonneg _)
    _ = Real.exp (argument * weight + radius * |weight|) / radius := by
      rw [Real.exp_add, mul_div_assoc]
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ positive.le
      by_cases nonnegative : 0 ≤ weight
      · rw [abs_of_nonneg nonnegative]
        have exponent_bound : argument * weight + radius * weight ≤ (upper + radius) * weight := by
          nlinarith [mul_le_mul_of_nonneg_right upper_bound nonnegative]
        exact (Real.exp_le_exp.mpr exponent_bound).trans
          (le_add_of_nonneg_left (Real.exp_nonneg _))
      · rw [abs_of_nonpos (le_of_not_ge nonnegative)]
        have exponent_bound : argument * weight + radius * -weight ≤ (lower - radius) * weight := by
          nlinarith [mul_le_mul_of_nonpos_right lower_bound (le_of_not_ge nonnegative)]
        exact (Real.exp_le_exp.mpr exponent_bound).trans
          (le_add_of_nonneg_right (Real.exp_nonneg _))

theorem exponential_vector_norm_le_endpoints
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (vector : E) (weight : ℝ) (parameter lower upper : ℂ)
    (lower_bound : lower.re ≤ parameter.re) (upper_bound : parameter.re ≤ upper.re) :
    ‖Complex.exp (parameter * (weight : ℂ)) • vector‖ ≤
      ‖Complex.exp (lower * (weight : ℂ)) • vector‖ +
        ‖Complex.exp (upper * (weight : ℂ)) • vector‖ := by
  simp only [norm_smul, Complex.norm_exp, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]
  by_cases nonnegative : 0 ≤ weight
  · exact (mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right upper_bound nonnegative))
      (norm_nonneg vector)).trans (le_add_of_nonneg_left (by positivity))
  · exact (mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right lower_bound (le_of_not_ge nonnegative)))
      (norm_nonneg vector)).trans (le_add_of_nonneg_right (by positivity))

theorem exponential_vector_deriv_norm_le_scaled
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (vector : E) (weight lower upper radius : ℝ) (parameter : ℂ)
    (positive : 0 < radius) (lower_bound : lower ≤ parameter.re) (upper_bound : parameter.re ≤ upper) :
    ‖deriv (fun nearby => Complex.exp (nearby * (weight : ℂ)) • vector) parameter‖ ≤
      (‖Complex.exp (((lower - radius : ℝ) : ℂ) * (weight : ℂ)) • vector‖ +
        ‖Complex.exp (((upper + radius : ℝ) : ℂ) * (weight : ℂ)) • vector‖) / radius := by
  rw [(exponential_vector_hasDerivAt vector weight parameter).deriv]
  simp only [norm_smul, norm_mul, Complex.norm_exp, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero, Complex.norm_real, Real.norm_eq_abs]
  calc
    _ ≤ ((Real.exp ((lower - radius) * weight) + Real.exp ((upper + radius) * weight)) / radius) * ‖vector‖ :=
      mul_le_mul_of_nonneg_right
        (real_exponential_weight_bound_scaled weight lower upper parameter.re radius positive lower_bound upper_bound)
        (norm_nonneg vector)
    _ = _ := by ring

theorem exponential_family_analytic
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {family : ℂ → X → E}
    (exponential : ∀ point, ∃ weight : ℝ, ∀ parameter,
      family parameter point = Complex.exp (parameter * (weight : ℂ)) • family 0 point)
    (point : X) (parameter : ℂ) : AnalyticAt ℂ (fun nearby => family nearby point) parameter := by
  obtain ⟨weight, scaling⟩ := exponential point
  rw [funext scaling]
  exact ((analyticAt_id.mul analyticAt_const).cexp).smul analyticAt_const

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
