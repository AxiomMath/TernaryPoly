module

public import TernaryPeriodPolynomials.Polynomial.Defs
public import TernaryPeriodPolynomials.Polynomial.Corollaries.PositiveCharacteristic

@[expose] public section


/-! Target: the positive-characteristic counterexample of Section 7.4. -/

open MvPolynomial TernaryPoly.Paper

namespace TernaryPeriodPolynomials

open TernaryPeriodPolynomials.Argument

/-- **Section 7.4, characteristic `p`.** Over every field of characteristic `p`, the product
`Π_p f̄_s` of the nonzero linear forms with the reduction of the degree-ten symmetric solution is
a nonzero solution of degree `p³ + 9` every monomial of which involves all three variables; in
particular it is not a sum of polynomials in two variables. -/
theorem positive_characteristic_counterexample (p : ℕ) [Fact p.Prime] (K : Type*) [Field K]
    [CharP K p] :
    Solution (nonzeroLinearFormProduct p K * symmetricTenSolution K) ∧
    nonzeroLinearFormProduct p K * symmetricTenSolution K ≠ 0 ∧
    (nonzeroLinearFormProduct p K * symmetricTenSolution K).IsHomogeneous (p ^ 3 + 9) ∧
    (∀ d ∈ (nonzeroLinearFormProduct p K * symmetricTenSolution K).support, ∀ i, 0 < d i) ∧
    ¬ TernaryPoly.Paper.Pairwise (nonzeroLinearFormProduct p K * symmetricTenSolution K) := by
  exact positiveChar_assembled p K

end TernaryPeriodPolynomials
