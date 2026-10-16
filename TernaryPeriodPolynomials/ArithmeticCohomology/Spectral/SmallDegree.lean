module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.Necessity
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.SmallDegreeLineBoundary

@[expose] public section


/-!
# Eigencharacter separation in degrees below three

In degrees `n < 3` both cuspidal boundary summands vanish
 (`SmallDegreeLineBoundary.associatePair_eq_bot_of_small_degree`, Sol AxiomCode), so separation of the associate pair is vacuous.
-/

open GeneralEisenstein

namespace TernaryPeriodPolynomials.Spectral

theorem eigenSeparated_of_small_degree {n : ℕ} (small : n < 3) (D : InducingData n)
    (hecke : BoundaryHecke n D.chi) :
    TernaryPeriodPolynomials.SpectralSeparation.EigenSeparated
      (awayThreeHeckeAlgebra D hecke) (associatePair D) :=
  eigenSeparated_of_eq_bot D hecke
    (TernaryPeriodPolynomials.EisensteinGraph.SmallDegreeLineBoundary.associatePair_eq_bot_of_small_degree
      small D)

end TernaryPeriodPolynomials.Spectral
