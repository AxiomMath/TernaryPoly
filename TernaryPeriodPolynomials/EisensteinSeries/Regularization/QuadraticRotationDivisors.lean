module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.QuadraticRotationApproximation

@[expose] public section


namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem circle_exponential_integer_shift (value : ℝ) (integer : ℤ) :
    Complex.exp (Complex.I * (↑(2 * Real.pi * (value - integer)) : ℂ)) =
      Complex.exp (Complex.I * (↑(2 * Real.pi * value) : ℂ)) := by
  have exponent : Complex.I * (↑(2 * Real.pi * (value - integer)) : ℂ) =
      Complex.I * (↑(2 * Real.pi * value) : ℂ) + ((-integer : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [exponent, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem circle_exponential_lower_bound (value : ℝ) (small : |value| ≤ 1 / 2) :
    4 * |value| ≤ ‖Complex.exp (Complex.I * (↑(2 * Real.pi * value) : ℂ)) - 1‖ := by
  have angle_nonnegative : 0 ≤ Real.pi * |value| := mul_nonneg Real.pi_pos.le (abs_nonneg _)
  have angle_small : Real.pi * |value| ≤ Real.pi / 2 := by nlinarith [Real.pi_pos]
  have sine := Real.mul_le_sin angle_nonnegative angle_small
  have coefficient : 2 / Real.pi * (Real.pi * |value|) = 2 * |value| := by field_simp
  rw [coefficient] at sine
  have absolute_sine : Real.sin (Real.pi * |value|) ≤ |Real.sin (Real.pi * value)| := by
    rcases le_total 0 value with nonnegative | nonpositive
    · rw [abs_of_nonneg nonnegative]
      exact le_abs_self _
    · rw [abs_of_nonpos nonpositive, mul_neg, Real.sin_neg]
      exact neg_le_abs _
  rw [Complex.norm_exp_I_mul_ofReal_sub_one,
    show 2 * Real.pi * value / 2 = Real.pi * value by ring,
    Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  linarith

theorem quadratic_rotation_phase_norm_lower (integer : ℤ) (nonzero : integer ≠ 0) :
    1 ≤ 5 * |(integer : ℝ)| *
      ‖fourier integer ((Real.sqrt 2 : ℝ) : AddCircle (1 : ℝ)) - 1‖ := by
  let value : ℝ := (integer : ℝ) * Real.sqrt 2
  have phase : fourier integer ((Real.sqrt 2 : ℝ) : AddCircle (1 : ℝ)) =
      Complex.exp (Complex.I * (↑(2 * Real.pi * value) : ℂ)) := by
    rw [fourier_coe_apply]
    congr 1
    dsimp only [value]
    push_cast
    ring
  rw [phase, ← circle_exponential_integer_shift value (round value)]
  have lower := circle_exponential_lower_bound (value - (round value : ℝ)) (abs_sub_round value)
  have arithmetic := sqrt_two_round_denominator_bound integer nonzero
  change 1 ≤ 5 * |(integer : ℝ)| * |value - (round value : ℝ)| at arithmetic
  have weakened : |value - (round value : ℝ)| ≤
      ‖Complex.exp (Complex.I * (↑(2 * Real.pi * (value - (round value : ℝ))) : ℂ)) - 1‖ := by
    linarith [abs_nonneg (value - (round value : ℝ))]
  exact arithmetic.trans (mul_le_mul_of_nonneg_left weakened (by positivity))

theorem quadratic_rotation_nonresonant (integer : ℤ) (nonzero : integer ≠ 0) :
    fourier integer ((Real.sqrt 2 : ℝ) : AddCircle (1 : ℝ)) ≠ 1 := by
  intro equal
  have lower := quadratic_rotation_phase_norm_lower integer nonzero
  rw [equal, sub_self, norm_zero, mul_zero] at lower
  norm_num at lower

theorem quadratic_rotation_inverse_bound (integer : ℤ) (nonzero : integer ≠ 0) :
    ‖(fourier integer ((Real.sqrt 2 : ℝ) : AddCircle (1 : ℝ)) - 1)⁻¹‖ ≤ 5 * |(integer : ℝ)| ^ 2 := by
  have norm_positive : 0 < ‖fourier integer ((Real.sqrt 2 : ℝ) : AddCircle (1 : ℝ)) - 1‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr (quadratic_rotation_nonresonant integer nonzero))
  have norm_lower := quadratic_rotation_phase_norm_lower integer nonzero
  have large : (1 : ℝ) ≤ |(integer : ℝ)| := by exact_mod_cast Int.one_le_abs nonzero
  rw [norm_inv]
  calc
    _ ≤ 5 * |(integer : ℝ)| := by
      rw [inv_eq_one_div]
      exact (div_le_iff₀ norm_positive).mpr norm_lower
    _ ≤ _ := by nlinarith

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
