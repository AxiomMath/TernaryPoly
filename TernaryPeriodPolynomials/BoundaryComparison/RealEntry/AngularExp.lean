module

public import TernaryPeriodPolynomials.BoundaryComparison.Defs

@[expose] public section


/-! Euler-formula expansion of `cos θ - i a sin θ` and its `m`-th power, used to turn
`angularIntegrand` into a finite trigonometric sum (Appendix C.5, `ar:eq:cinfty`). -/


namespace TernaryPeriodPolynomials.Argument

theorem cos_sub_I_mul_mul_sin_eq (a θ : ℝ) :
    (Real.cos θ : ℂ) - Complex.I * (a : ℂ) * (Real.sin θ : ℂ) =
      ((1 - a) * Complex.exp (Complex.I * θ) + (1 + a) * Complex.exp (-(Complex.I * θ))) / 2 := by
  rw [Complex.ofReal_cos, Complex.ofReal_sin]
  have h1 : Complex.exp (Complex.I * (θ : ℂ)) =
      Complex.cos (θ : ℂ) + Complex.sin (θ : ℂ) * Complex.I := by
    rw [mul_comm Complex.I (θ : ℂ)]; exact Complex.exp_mul_I _
  have h2 : Complex.exp (-(Complex.I * (θ : ℂ))) =
      Complex.cos (θ : ℂ) - Complex.sin (θ : ℂ) * Complex.I := by
    have e : -(Complex.I * (θ : ℂ)) = (-(θ : ℂ)) * Complex.I := by ring
    rw [e, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
    ring
  rw [h1, h2]; ring

theorem cos_sub_I_mul_mul_sin_pow (a θ : ℝ) (m : ℕ) :
    ((Real.cos θ : ℂ) - Complex.I * (a : ℂ) * (Real.sin θ : ℂ)) ^ m =
      (∑ j ∈ Finset.range (m + 1),
        (m.choose j : ℂ) * (1 - (a:ℂ))^j * (1 + (a:ℂ))^(m-j) *
          (Complex.exp (Complex.I * θ))^j * (Complex.exp (-(Complex.I * θ)))^(m-j)) / 2^m := by
  rw [cos_sub_I_mul_mul_sin_eq, div_pow, add_pow]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [mul_pow, mul_pow]
  ring

end TernaryPeriodPolynomials.Argument
