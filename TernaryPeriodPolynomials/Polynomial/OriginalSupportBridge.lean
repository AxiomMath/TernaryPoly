module

public import TernaryPeriodPolynomials.Polynomial.RationalPairwise
public import TernaryPeriodPolynomials.Polynomial.Definitions

@[expose] public section


/-! Connect the existing scalar-extension library to the new Eisenstein proof. -/
namespace TernaryPoly.Paper

/-- Rational support, with its scalar input derived from the child statements. -/
theorem rational_solution_pairwise (f : Ternary ℚ) (hf : Solution f) : Pairwise f := by
  apply (TernaryPoly.pairwise_iff_exists_rename f).mpr
  exact TernaryPeriodPolynomials.ternary_period_polynomial_pairwise f hf.1 hf.2

end TernaryPoly.Paper
