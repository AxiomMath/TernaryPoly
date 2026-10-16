module

public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.EbarReduceTwoForms
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Base.Cases

@[expose] public section


open MvPolynomial TernaryPoly.CharTwoNorm

namespace TernaryPeriodPolynomials.Argument.ModFourBeta

/-- Splitting `piOperator` as the sum over a prefix and the matching suffix of
`piSubstitutions`, for any cut point `n`. Purely a `List.take`/`List.drop` fact,
independent of what the eighteen substitutions actually are. -/
theorem piOperator_take_drop (h : Poly2) (n : ℕ) :
    piOperator h = ((piSubstitutions.take n).map fun t => bind₁ t h).sum +
        ((piSubstitutions.drop n).map fun t => bind₁ t h).sum := by
  conv_lhs => rw [piOperator, ← List.take_append_drop n piSubstitutions, List.map_append,
    List.sum_append]

end TernaryPeriodPolynomials.Argument.ModFourBeta
