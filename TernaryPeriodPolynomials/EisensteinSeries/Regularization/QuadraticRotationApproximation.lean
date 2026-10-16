module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.CircleSmallDivisorCriterion

@[expose] public section


namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem sqrt_two_integer_product (integer nearest : ℤ) :
    ((integer : ℝ) * Real.sqrt 2 - nearest) * ((integer : ℝ) * Real.sqrt 2 + nearest) =
      ((2 * integer ^ 2 - nearest ^ 2 : ℤ) : ℝ) := by
  calc
    _ = (integer : ℝ) ^ 2 * (Real.sqrt 2) ^ 2 - (nearest : ℝ) ^ 2 := by ring
    _ = _ := by rw [Real.sq_sqrt (by norm_num)]; push_cast; ring

theorem sqrt_two_integer_product_ne_zero (integer nearest : ℤ) (nonzero : integer ≠ 0) :
    2 * integer ^ 2 - nearest ^ 2 ≠ 0 := by
  intro zero
  have irrational := irrational_sqrt_two.intCast_mul nonzero
  have product : ((integer : ℝ) * Real.sqrt 2 - nearest) * ((integer : ℝ) * Real.sqrt 2 + nearest) = 0 := by
    rw [sqrt_two_integer_product, zero, Int.cast_zero]
  rcases mul_eq_zero.mp product with first | second
  · exact irrational.ne_int nearest (sub_eq_zero.mp first)
  · apply irrational.ne_int (-nearest)
    push_cast
    linarith

theorem sqrt_two_round_denominator_bound (integer : ℤ) (nonzero : integer ≠ 0) :
    1 ≤ 5 * |(integer : ℝ)| *
      |(integer : ℝ) * Real.sqrt 2 - (round ((integer : ℝ) * Real.sqrt 2) : ℝ)| := by
  let nearest : ℤ := round ((integer : ℝ) * Real.sqrt 2)
  have integer_large : (1 : ℝ) ≤ |(integer : ℝ)| := by exact_mod_cast Int.one_le_abs nonzero
  have sqrt_nonnegative := Real.sqrt_nonneg (2 : ℝ)
  have sqrt_small : Real.sqrt 2 ≤ 2 := by nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have distance : |(integer : ℝ) * Real.sqrt 2 - nearest| ≤ 1 / 2 := abs_sub_round _
  have nearest_bound : |(nearest : ℝ)| ≤ 3 * |(integer : ℝ)| := by
    calc
      _ ≤ |(nearest : ℝ) - (integer : ℝ) * Real.sqrt 2| + |(integer : ℝ) * Real.sqrt 2| := by
        convert! abs_add_le ((nearest : ℝ) - (integer : ℝ) * Real.sqrt 2)
          ((integer : ℝ) * Real.sqrt 2) using 1
        ring_nf
      _ ≤ 1 / 2 + 2 * |(integer : ℝ)| := by
        rw [abs_sub_comm, abs_mul, abs_of_nonneg sqrt_nonnegative]
        have product := mul_le_mul_of_nonneg_left sqrt_small (abs_nonneg (integer : ℝ))
        linarith
      _ ≤ _ := by linarith
  have factor_bound : |(integer : ℝ) * Real.sqrt 2 + nearest| ≤ 5 * |(integer : ℝ)| := by
    calc
      _ ≤ |(integer : ℝ) * Real.sqrt 2| + |(nearest : ℝ)| := abs_add_le _ _
      _ ≤ _ := by
        rw [abs_mul, abs_of_nonneg sqrt_nonnegative]
        have product := mul_le_mul_of_nonneg_left sqrt_small (abs_nonneg (integer : ℝ))
        linarith
  have norm_large : (1 : ℝ) ≤ |((2 * integer ^ 2 - nearest ^ 2 : ℤ) : ℝ)| := by
    exact_mod_cast Int.one_le_abs (sqrt_two_integer_product_ne_zero integer nearest nonzero)
  rw [← sqrt_two_integer_product, abs_mul] at norm_large
  have enlarged := mul_le_mul_of_nonneg_left factor_bound
    (abs_nonneg ((integer : ℝ) * Real.sqrt 2 - nearest))
  change 1 ≤ 5 * |(integer : ℝ)| * |(integer : ℝ) * Real.sqrt 2 - nearest|
  nlinarith

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
