module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs
public import TernaryPeriodPolynomials.SymmetricSolution.ObstructionVanishing.Bernoulli

@[expose] public section


/-! Target: Proposition 4.2 (`thm:J-vanishes`) of the paper (Appendix C; no Harder–Raghuram graph theorem, Hecke projection, or statement of
`TernaryPeriodPolynomials`). -/

open GeneralEisenstein

namespace TernaryPeriodPolynomials

open TernaryPeriodPolynomials.Argument

/-- **Proposition 4.2.** Every symmetric homogeneous solution of positive degree satisfies
`J_f = 0`, for the literal Bernoulli obstruction of equation `eq:Jdef`. -/
theorem symmetric_obstruction_vanishes (n : ℕ) (hn : 0 < n) (f : HomogeneousPoly n) (hf : SymmetricSolution f) :
    bernoulliObstruction f = 0 := by
  exact TernaryPeriodPolynomials.Argument.Classification.symmetric_obstruction_vanishes_of_route n hn f hf

end TernaryPeriodPolynomials
