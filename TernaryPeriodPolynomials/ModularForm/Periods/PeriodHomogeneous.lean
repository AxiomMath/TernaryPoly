module

public import TernaryPeriodPolynomials.PeriodPolynomial.Defs
public import TernaryPeriodPolynomials.Polynomial.Homogeneous

@[expose] public section



/-!
# Homogeneity of the Mellin period polynomials

`periodPolynomial n h` is manifestly a sum of monomials `C c * X0^(n-j) * X1^j`, hence homogeneous
of degree `n`; `evenPeriodPart` inherits this since `bind₁ ![-X 0, X 1]` is a linear substitution
(`TernaryPoly.isHomogeneous_bind₁_linear`), and the `(2:ℂ)⁻¹` scalar factor does not change degree.
-/

noncomputable section
open MvPolynomial TernaryPoly

namespace TernaryPeriodPolynomials.Argument.CuspForms

theorem periodPolynomial_isHomogeneous {n : ℕ} {k : ℤ} (h : CuspForm levelOne k) :
    (TernaryPeriodPolynomials.Argument.periodPolynomial n h).IsHomogeneous n := by
  rw [TernaryPeriodPolynomials.Argument.periodPolynomial]
  apply MvPolynomial.IsHomogeneous.sum
  intro j hj
  simp only [Finset.mem_range] at hj
  have hjn : n - j + j = n := Nat.sub_add_cancel (by omega)
  have hh := (MvPolynomial.isHomogeneous_C_mul_X_pow
      ((n.choose j : ℂ) * (-1) ^ (n - j) * Complex.I ^ (j + 1) *
        TernaryPeriodPolynomials.Argument.periodMoment h j) (0 : Fin 2) (n - j)).mul
      (MvPolynomial.isHomogeneous_X_pow (1 : Fin 2) j)
  rwa [hjn] at hh

theorem evenPeriodPart_isHomogeneous {n : ℕ} {k : ℤ} (h : CuspForm levelOne k) :
    (TernaryPeriodPolynomials.Argument.evenPeriodPart n h).IsHomogeneous n := by
  rw [TernaryPeriodPolynomials.Argument.evenPeriodPart, MvPolynomial.smul_eq_C_mul]
  apply MvPolynomial.IsHomogeneous.C_mul
  apply (periodPolynomial_isHomogeneous h).add
  apply isHomogeneous_bind₁_linear (periodPolynomial_isHomogeneous h)
  intro i
  fin_cases i
  · exact (MvPolynomial.isHomogeneous_X ℂ (0 : Fin 2)).neg
  · exact MvPolynomial.isHomogeneous_X ℂ _

/-- The axis-correction monomial `X0^n - X1^n` is homogeneous of degree `n`. -/
theorem axisMonomial_isHomogeneous (n : ℕ) :
    (X 0 ^ n - X 1 ^ n : MvPolynomial (Fin 2) ℂ).IsHomogeneous n :=
  (MvPolynomial.isHomogeneous_X_pow (0 : Fin 2) n).sub (MvPolynomial.isHomogeneous_X_pow (1 : Fin 2) n)

theorem normalizedEvenPeriodPart_isHomogeneous {n : ℕ} {k : ℤ} (h : CuspForm levelOne k) :
    (TernaryPeriodPolynomials.Argument.normalizedEvenPeriodPart n h).IsHomogeneous n := by
  rw [TernaryPeriodPolynomials.Argument.normalizedEvenPeriodPart]
  exact (evenPeriodPart_isHomogeneous h).sub ((axisMonomial_isHomogeneous n).C_mul _)

end TernaryPeriodPolynomials.Argument.CuspForms
