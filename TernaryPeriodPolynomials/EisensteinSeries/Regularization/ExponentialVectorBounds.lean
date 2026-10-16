module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Normalized.VectorParameters
public import Mathlib.Analysis.Calculus.MeanValue

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem real_exponential_weight_bound (weight lower upper argument : ℝ)
    (lower_bound : lower ≤ argument) (upper_bound : argument ≤ upper) :
    Real.exp (argument * weight) * |weight| ≤
      Real.exp ((lower - 1) * weight) + Real.exp ((upper + 1) * weight) := by
  by_cases nonnegative : 0 ≤ weight
  · rw [abs_of_nonneg nonnegative]
    have weight_bound : weight ≤ Real.exp weight := by linarith [Real.add_one_le_exp weight]
    calc
      _ ≤ Real.exp (argument * weight) * Real.exp weight :=
        mul_le_mul_of_nonneg_left weight_bound (Real.exp_nonneg _)
      _ = Real.exp ((argument + 1) * weight) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp ((upper + 1) * weight) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by linarith : argument + 1 ≤ upper + 1) nonnegative)
      _ ≤ _ := le_add_of_nonneg_left (Real.exp_nonneg _)
  · have nonpositive : weight ≤ 0 := le_of_not_ge nonnegative
    rw [abs_of_nonpos nonpositive]
    have weight_bound : -weight ≤ Real.exp (-weight) := by linarith [Real.add_one_le_exp (-weight)]
    calc
      _ ≤ Real.exp (argument * weight) * Real.exp (-weight) :=
        mul_le_mul_of_nonneg_left weight_bound (Real.exp_nonneg _)
      _ = Real.exp ((argument - 1) * weight) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp ((lower - 1) * weight) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right (sub_le_sub_right lower_bound 1) nonpositive)
      _ ≤ _ := le_add_of_nonneg_right (Real.exp_nonneg _)

theorem exponential_vector_hasDerivAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (vector : E) (weight : ℝ) (parameter : ℂ) :
    HasDerivAt (fun nearby => Complex.exp (nearby * (weight : ℂ)) • vector)
      ((Complex.exp (parameter * (weight : ℂ)) * (weight : ℂ)) • vector) parameter := by
  simpa only [one_mul, id_eq] using (((hasDerivAt_id parameter).mul_const (weight : ℂ)).cexp).smul_const vector

theorem exponential_vector_deriv_norm_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (vector : E) (weight lower upper : ℝ) (parameter : ℂ)
    (lower_bound : lower ≤ parameter.re) (upper_bound : parameter.re ≤ upper) :
    ‖deriv (fun nearby => Complex.exp (nearby * (weight : ℂ)) • vector) parameter‖ ≤
      ‖Complex.exp (((lower - 1 : ℝ) : ℂ) * (weight : ℂ)) • vector‖ +
        ‖Complex.exp (((upper + 1 : ℝ) : ℂ) * (weight : ℂ)) • vector‖ := by
  rw [(exponential_vector_hasDerivAt vector weight parameter).deriv]
  simp only [norm_smul, norm_mul, Complex.norm_exp, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero, Complex.norm_real, Real.norm_eq_abs]
  rw [← add_mul]
  exact mul_le_mul_of_nonneg_right (real_exponential_weight_bound weight lower upper parameter.re
    lower_bound upper_bound) (norm_nonneg vector)

theorem exponential_vector_difference_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (vector : E) (weight lower upper : ℝ) (first second : ℂ)
    (first_bound : lower ≤ first.re ∧ first.re ≤ upper)
    (second_bound : lower ≤ second.re ∧ second.re ≤ upper) :
    ‖Complex.exp (second * (weight : ℂ)) • vector - Complex.exp (first * (weight : ℂ)) • vector‖ ≤
      (‖Complex.exp (((lower - 1 : ℝ) : ℂ) * (weight : ℂ)) • vector‖ +
        ‖Complex.exp (((upper + 1 : ℝ) : ℂ) * (weight : ℂ)) • vector‖) * ‖second - first‖ := by
  exact Convex.norm_image_sub_le_of_norm_deriv_le
    (fun parameter (_ : parameter ∈ Complex.re ⁻¹' Set.Icc lower upper) =>
      (exponential_vector_hasDerivAt vector weight parameter).differentiableAt)
    (fun parameter member => exponential_vector_deriv_norm_le vector weight lower upper parameter member.1 member.2)
    ((convex_Icc lower upper).linear_preimage Complex.reLm) first_bound second_bound

theorem normalizedCuspVector_deriv_norm_le
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (matrix : AdelicGL) (lower upper : ℝ) (parameter : ℂ)
    (lower_bound : lower ≤ parameter.re) (upper_bound : parameter.re ≤ upper) :
    ‖deriv (fun nearby => (normalizedCuspVector flat.1 nearby matrix).val) parameter‖ ≤
      ‖(normalizedCuspVector flat.1 ((lower - 1 : ℝ) : ℂ) matrix).val‖ +
        ‖(normalizedCuspVector flat.1 ((upper + 1 : ℝ) : ℂ) matrix).val‖ := by
  obtain ⟨weight, scaling⟩ := normalizedCuspVector_exponential flat matrix
  have values (nearby : ℂ) : (normalizedCuspVector flat.1 nearby matrix).val =
      Complex.exp (nearby * (weight : ℂ)) • (normalizedCuspVector flat.1 0 matrix).val :=
    congrArg Subtype.val (scaling nearby)
  have function_eq := funext values
  rw [function_eq, values ((lower - 1 : ℝ) : ℂ), values ((upper + 1 : ℝ) : ℂ)]
  exact exponential_vector_deriv_norm_le _ weight lower upper parameter lower_bound upper_bound

theorem normalizedCuspVector_difference_bound
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (matrix : AdelicGL) (lower upper : ℝ) (first second : ℂ)
    (first_bound : lower ≤ first.re ∧ first.re ≤ upper)
    (second_bound : lower ≤ second.re ∧ second.re ≤ upper) :
    ‖(normalizedCuspVector flat.1 second matrix).val - (normalizedCuspVector flat.1 first matrix).val‖ ≤
      (‖(normalizedCuspVector flat.1 ((lower - 1 : ℝ) : ℂ) matrix).val‖ +
        ‖(normalizedCuspVector flat.1 ((upper + 1 : ℝ) : ℂ) matrix).val‖) * ‖second - first‖ := by
  obtain ⟨weight, scaling⟩ := normalizedCuspVector_exponential flat matrix
  have values (nearby : ℂ) : (normalizedCuspVector flat.1 nearby matrix).val =
      Complex.exp (nearby * (weight : ℂ)) • (normalizedCuspVector flat.1 0 matrix).val :=
    congrArg Subtype.val (scaling nearby)
  rw [values second, values first, values ((lower - 1 : ℝ) : ℂ), values ((upper + 1 : ℝ) : ℂ)]
  exact exponential_vector_difference_bound _ weight lower upper first second first_bound second_bound

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
