module

public import TernaryPeriodPolynomials.BoundaryComparison.Defs

@[expose] public section


/-! Clause 4 of `real_constant_term_entry`: the claimed value `-2πi/(n+1)` is nonzero. -/


namespace TernaryPeriodPolynomials.Argument

/-- **Clause 4 of `real_constant_term_entry`.** -/
theorem real_constant_term_nonvanishing (n : ℕ) :
    -2 * Real.pi * Complex.I / ((n:ℂ)+1) ≠ 0 := by
  apply div_ne_zero
  · exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero))
      Complex.I_ne_zero
  · have heq : ((n:ℂ)+1) = ((n+1:ℕ):ℂ) := by push_cast; ring
    rw [heq]
    exact Nat.cast_ne_zero.mpr (by omega)

end TernaryPeriodPolynomials.Argument
