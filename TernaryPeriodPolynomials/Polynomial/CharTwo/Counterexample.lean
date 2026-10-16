module

public import TernaryPeriodPolynomials.Polynomial.Defs
public import TernaryPeriodPolynomials.Polynomial.Corollaries.CharacteristicTwo

@[expose] public section


/-! Target: the characteristic-two example of degree eleven in Section 7.4. -/

open MvPolynomial TernaryPoly.Paper

namespace TernaryPeriodPolynomials

open TernaryPeriodPolynomials.Argument

/-- **Section 7.4, characteristic two.** Modulo two `D̄ = Φ(X³Y + XY³)` is a solution,
`xyz D̄` is the product of the seven nonzero linear forms over `𝔽₂`, and `g = xyz D̄²` is a
nonzero solution of odd degree eleven violating two-variable support. -/
theorem characteristic_two_counterexample :
    universalDivisor (ZMod 2) =
      cyclicLift (X 0 ^ 3 * X 1 + X 0 * X 1 ^ 3 : MvPolynomial (Fin 2) (ZMod 2)) ∧
    Solution (universalDivisor (ZMod 2)) ∧
    X 0 * X 1 * X 2 * universalDivisor (ZMod 2) = nonzeroLinearFormProduct 2 (ZMod 2) ∧
    Solution (X 0 * X 1 * X 2 * universalDivisor (ZMod 2) ^ 2) ∧
    X 0 * X 1 * X 2 * universalDivisor (ZMod 2) ^ 2 ≠ 0 ∧
    (X 0 * X 1 * X 2 * universalDivisor (ZMod 2) ^ 2).IsHomogeneous 11 ∧
    ¬ TernaryPoly.Paper.Pairwise (X 0 * X 1 * X 2 * universalDivisor (ZMod 2) ^ 2) := by
  exact ⟨charTwo_universalDivisor_eq, charTwo_solution_universalDivisor,
    charTwo_nonzeroProduct_eq, charTwo_solution_nonzeroProduct, charTwo_f_ne_zero,
    charTwo_f_isHomogeneous, charTwo_not_pairwise⟩

end TernaryPeriodPolynomials
