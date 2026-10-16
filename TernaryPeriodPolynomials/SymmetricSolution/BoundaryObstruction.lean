module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs
public import TernaryPeriodPolynomials.SymmetricSolution.BoundaryObstruction.EndpointPull

@[expose] public section


/-! Target: the boundary statement proved in Proposition 4.2 (`thm:J-vanishes`). -/

open GeneralEisenstein GeneralEisenstein.Homogeneous

namespace TernaryPeriodPolynomials

open TernaryPeriodPolynomials.Argument

/-- **Proposition 4.2, boundary form.** For `n ≥ 4`, a global degree-two class with coefficients
`E_n` whose line restriction is mixed cuspidal (zero at every complete flag) and whose restrictions
vanish at every good vertex has zero line restriction. (In the paper this is applied to the
connecting class `a_F`; Lemma 4.1 then gives `J_f = 0`.) -/
theorem line_restriction_eq_zero_of_good_vertices (n : ℕ) (hn : 4 ≤ n)
    (c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter))
    (hline : InnerBoundary n trivialCharacter .line (globalCoordinates n trivialCharacter c).2)
    (hgood : GoodBoundaryVanishing n trivialCharacter (globalCoordinates n trivialCharacter c)) :
    (globalCoordinates n trivialCharacter c).2 = 0 := by
  exact TernaryPeriodPolynomials.Argument.Classification.line_restriction_eq_zero_of_good_vertices_of_route n hn c hline hgood

end TernaryPeriodPolynomials
