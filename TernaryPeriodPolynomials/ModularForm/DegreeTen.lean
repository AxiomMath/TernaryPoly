module

public import TernaryPeriodPolynomials.Polynomial.Defs
public import TernaryPeriodPolynomials.PeriodPolynomial.Defs
public import TernaryPeriodPolynomials.ModularForm.Periods.ExampleDegreeTenAssembly

@[expose] public section


/-! Target: the degree-ten Example of the introduction of the paper. -/

open MvPolynomial TernaryPoly.Paper

namespace TernaryPeriodPolynomials

open TernaryPeriodPolynomials.Argument

/-- **Example (degree ten).** `q_s` and `q_a` satisfy the normalized period relations; `q_s` is
symmetric and odd in each variable and `q_a` is alternating and even in each variable; the cyclic
sums `f_s = Φ(q_s)`, `f_a = Φ(q_a)` form a basis of `W₁₀(F)`; and over `ℂ` they are nonzero
multiples of the odd and normalized even period polynomials of the weight-twelve cusp form. -/
theorem example_degree_ten :
    (∀ (F : Type) [Field F] [CharZero F],
      symmetricTenPeriod F ∈ oddPeriodSpace F 10 ∧ alternatingTenPeriod F ∈ evenPeriodSpace F 10 ∧
      bind₁ ![X 1, X 0] (symmetricTenPeriod F) = symmetricTenPeriod F ∧
      bind₁ ![-X 0, X 1] (symmetricTenPeriod F) = -symmetricTenPeriod F ∧
      bind₁ ![X 0, -X 1] (symmetricTenPeriod F) = -symmetricTenPeriod F ∧
      bind₁ ![X 1, X 0] (alternatingTenPeriod F) = -alternatingTenPeriod F ∧
      bind₁ ![-X 0, X 1] (alternatingTenPeriod F) = alternatingTenPeriod F ∧
      bind₁ ![X 0, -X 1] (alternatingTenPeriod F) = alternatingTenPeriod F ∧
      LinearIndependent F ![symmetricTenSolution F, alternatingTenSolution F] ∧
      Submodule.span F {symmetricTenSolution F, alternatingTenSolution F} = solutionSpace F 10) ∧
    ∀ h : CuspForm levelOne 12, h ≠ 0 →
      (∃ c : ℂ, c ≠ 0 ∧ symmetricTenPeriod ℂ = c • oddPeriodPart 10 h) ∧
      (∃ c : ℂ, c ≠ 0 ∧ alternatingTenPeriod ℂ = c • normalizedEvenPeriodPart 10 h) :=
  TernaryPeriodPolynomials.Argument.CuspForms.example_degree_ten_proof

end TernaryPeriodPolynomials
