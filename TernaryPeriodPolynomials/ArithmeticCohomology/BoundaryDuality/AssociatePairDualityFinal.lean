module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Local.PairingL2
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Local.PairingCaseL1TrivialFinal
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Local.LocalPairingCaseL1OddUnconditional
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Local.PairingCaseL0OddFinal
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Local.PairingCaseL0EvenFinal
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.SmallDegreeLineBoundary

@[expose] public section


/-!
# Boundary duality on the associate pair

For every inducing datum, boundary duality on the associate pair holds (`associatePairDuality`):
every nonzero class of the line summand has a plane summand class whose boundary cup product with
it is not exact in the boundary building. In degree at least three this is assembled from local
nondegeneracy at the two line cusps: the good line for the trivial and for a nontrivial character,
and the bad line for the trivial character in even and in odd degree. In degree below three the
line summand is zero.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein

namespace TernaryPeriodPolynomials.BoundaryDuality.AssociatePairDualityFinal

open TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.BoundaryDuality.ParityCases

variable {n : ℕ}

/-- **Boundary duality on the associate pair from the two bad-line inputs.** -/
theorem associatePairDuality_of_badLine (hn : 3 ≤ n) (D : InducingData n)
    (badEven : BadLineEvenInput n) (badOdd : BadLineOddInput n) : AssociatePairDuality D :=
  LocalPairingL2.associatePairDuality_of_cases hn D
    (LocalPairingCaseL1TrivialFinal.goodLineTrivialInput_unconditional hn)
    (LocalPairingCaseL1OddUnconditional.goodLineNontrivialInput_unconditional hn) badEven badOdd

/-- **Boundary duality on the associate pair from the even-degree bad-line input.** -/
theorem associatePairDuality_of_badLineEven (hn : 3 ≤ n) (D : InducingData n)
    (badEven : BadLineEvenInput n) : AssociatePairDuality D :=
  associatePairDuality_of_badLine hn D badEven
    (LocalPairingCaseL0Odd.badLineOddInput_unconditional hn)

/-- **Boundary duality on the associate pair in degree at least three.** -/
theorem associatePairDuality_of_three_le (hn : 3 ≤ n) (D : InducingData n) :
    AssociatePairDuality D :=
  associatePairDuality_of_badLineEven hn D
    (LocalPairingCaseL0Even.badLineEvenInput_unconditional hn)

/-- **Boundary duality on the associate pair**, for every inducing datum. -/
theorem associatePairDuality (D : InducingData n) : AssociatePairDuality D := by
  rcases Nat.lt_or_ge n 3 with small | large
  · exact CoordinateInputs.associatePairDuality_of_eq_bot D
      (EisensteinGraph.SmallDegreeLineBoundary.associatePair_eq_bot_of_small_degree small D)
  · exact associatePairDuality_of_three_le large D

end TernaryPeriodPolynomials.BoundaryDuality.AssociatePairDualityFinal
