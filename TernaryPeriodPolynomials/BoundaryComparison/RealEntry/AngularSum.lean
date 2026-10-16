module

public import TernaryPeriodPolynomials.BoundaryComparison.RealEntry.AngularExp

@[expose] public section


/-! Rewrites `angularIntegrand n r θ` as a double finite sum, over `j ∈ range 4` and
`l ∈ range (n+1)`, of a θ-independent coefficient times a single complex exponential
`exp(i·2(j+l)·θ)` (Appendix C.5, `ar:eq:cinfty`). Binomial-expands each cubic/`n`-th factor via
`cos_sub_I_mul_mul_sin_pow`, then collapses the resulting product of five exponentials via
`exp_combine`. -/


namespace TernaryPeriodPolynomials.Argument

theorem angularIntegrand_eq_doublesum (n : ℕ) (r θ : ℝ) :
    angularIntegrand n r θ =
      (∑ j ∈ Finset.range 4, ∑ l ∈ Finset.range (n+1),
        Complex.exp (Complex.I*((n:ℂ)+3)*θ) *
        ((((3:ℕ).choose j:ℂ) * (1-(r:ℂ))^j * (1+(r:ℂ))^(3-j) *
          (Complex.exp (Complex.I*θ))^j * (Complex.exp (-(Complex.I*θ)))^(3-j)) *
         ((n.choose l:ℂ) * (1-((1/r:ℝ):ℂ))^l * (1+((1/r:ℝ):ℂ))^(n-l) *
          (Complex.exp (Complex.I*θ))^l * (Complex.exp (-(Complex.I*θ)))^(n-l)))) /
        (2^3 * 2^n) := by
  have hdiv : (Real.cos θ:ℂ) - Complex.I*(Real.sin θ:ℂ)/(r:ℂ) =
      (Real.cos θ:ℂ) - Complex.I*((1/r:ℝ):ℂ)*(Real.sin θ:ℂ) := by push_cast; ring
  unfold angularIntegrand
  rw [hdiv, cos_sub_I_mul_mul_sin_pow r θ 3, cos_sub_I_mul_mul_sin_pow (1/r) θ n]
  have hfield : ∀ (e X Y : ℂ), e * (X/2^3) * (Y/2^n) = e*(X*Y)/(2^3*2^n) := by
    intro e X Y; ring
  rw [hfield, Finset.sum_mul_sum, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum]

theorem exp_combine (n j l : ℕ) (hj : j ≤ 3) (hl : l ≤ n) (θ : ℝ) :
    Complex.exp (Complex.I * ((n:ℂ)+3) * θ) *
      (Complex.exp (Complex.I*θ))^j * (Complex.exp (-(Complex.I*θ)))^(3-j) *
      (Complex.exp (Complex.I*θ))^l * (Complex.exp (-(Complex.I*θ)))^(n-l) =
      Complex.exp (Complex.I * (2*((j:ℂ)+l)) * θ) := by
  rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul,
      ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  have h3 : ((3 - j : ℕ) : ℂ) = (3:ℂ) - (j:ℂ) := Nat.cast_sub hj
  have hn : ((n - l : ℕ) : ℂ) = (n:ℂ) - (l:ℂ) := Nat.cast_sub hl
  rw [h3, hn]
  ring

theorem angularIntegrand_eq_doublesum2 (n : ℕ) (r θ : ℝ) :
    angularIntegrand n r θ =
      (∑ j ∈ Finset.range 4, ∑ l ∈ Finset.range (n+1),
        (((3:ℕ).choose j:ℂ) * (1-(r:ℂ))^j * (1+(r:ℂ))^(3-j)) *
        ((n.choose l:ℂ) * (1-((1/r:ℝ):ℂ))^l * (1+((1/r:ℝ):ℂ))^(n-l)) *
        Complex.exp (Complex.I*(2*((j:ℂ)+l))*θ)) / (2^3 * 2^n) := by
  rw [angularIntegrand_eq_doublesum]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro l hl
  rw [Finset.mem_range] at hj hl
  have hcombine := exp_combine n j l (by omega) (by omega) θ
  calc Complex.exp (Complex.I*((n:ℂ)+3)*θ) *
        ((((3:ℕ).choose j:ℂ) * (1-(r:ℂ))^j * (1+(r:ℂ))^(3-j) *
          (Complex.exp (Complex.I*θ))^j * (Complex.exp (-(Complex.I*θ)))^(3-j)) *
         ((n.choose l:ℂ) * (1-((1/r:ℝ):ℂ))^l * (1+((1/r:ℝ):ℂ))^(n-l) *
          (Complex.exp (Complex.I*θ))^l * (Complex.exp (-(Complex.I*θ)))^(n-l)))
      = (((3:ℕ).choose j:ℂ) * (1-(r:ℂ))^j * (1+(r:ℂ))^(3-j)) *
        ((n.choose l:ℂ) * (1-((1/r:ℝ):ℂ))^l * (1+((1/r:ℝ):ℂ))^(n-l)) *
        (Complex.exp (Complex.I*((n:ℂ)+3)*θ) * (Complex.exp (Complex.I*θ))^j *
          (Complex.exp (-(Complex.I*θ)))^(3-j) * (Complex.exp (Complex.I*θ))^l *
          (Complex.exp (-(Complex.I*θ)))^(n-l)) := by ring
    _ = (((3:ℕ).choose j:ℂ) * (1-(r:ℂ))^j * (1+(r:ℂ))^(3-j)) *
        ((n.choose l:ℂ) * (1-((1/r:ℝ):ℂ))^l * (1+((1/r:ℝ):ℂ))^(n-l)) *
        Complex.exp (Complex.I*(2*((j:ℂ)+l))*θ) := by rw [hcombine]

end TernaryPeriodPolynomials.Argument
