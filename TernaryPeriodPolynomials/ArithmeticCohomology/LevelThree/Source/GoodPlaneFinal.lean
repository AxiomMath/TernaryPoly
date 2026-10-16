module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Source.GoodPlaneRealization
public import TernaryPeriodPolynomials.ArithmeticCohomology.PeriodLink.Final

@[expose] public section


/-!
# Source realization at the good plane, unconditionally (trivial character, odd degree)

Workstream PL proves the level-three period nonvanishing `LevelThreePeriodNonvanishing n` for every
`n` (`PeriodLink.levelThreePeriodNonvanishing`, from the injectivity of the level-three
period map).  With `GoodPlaneRealization` this gives, for the trivial character and odd degree:

* source realization at the good plane (`sourceRealization_goodPlane`);
* summand nonvanishing at the good plane (`levelThreeSummandNonvanishing_goodPlane`);
* the rank lower bound at the good plane from the local bound `2` and the oldform
  classes alone (`coordinateRankLowerBound_goodPlane_of_bound_oldform`).

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein
open TernaryPeriodPolynomials.SpectralSeparation
open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.Separation

namespace TernaryPeriodPolynomials.LevelThreeSource

variable {n : ℕ}

/-- **Source realization at the good plane** (trivial character, odd degree, nonzero pair). -/
theorem sourceRealization_goodPlane (hodd : Odd n) (D : InducingData n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke)
    (hχ : D.chi = trivialCharacter) (hne : associatePair D ≠ ⊥) :
    SourceRealization D hecke hhecke .plane true :=
  sourceRealization_goodPlane_of_periodNonvanishing hodd
    (TernaryPeriodPolynomials.PeriodLink.levelThreePeriodNonvanishing n)
    D hecke hhecke hχ hne

/-- **Summand nonvanishing at the good plane** (trivial character, odd degree). -/
theorem levelThreeSummandNonvanishing_goodPlane (hodd : Odd n) (D : InducingData n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke)
    (hχ : D.chi = trivialCharacter) :
    LevelThreeSummandNonvanishing D hecke hhecke .plane true :=
  levelThreeSummandNonvanishing_goodPlane_of_periodNonvanishing hodd
    (TernaryPeriodPolynomials.PeriodLink.levelThreePeriodNonvanishing n)
    D hecke hhecke hχ

/-- **The rank lower bound at the good plane** (trivial character, odd degree) from D's local
bound and the oldform classes. -/
theorem coordinateRankLowerBound_goodPlane_of_bound_oldform (hodd : Odd n) (D : InducingData n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke)
    (hχ : D.chi = trivialCharacter)
    (hbound : associatePair D ≠ ⊥ →
      LocalUpperBound n D.chi (pairCharacter D hecke hhecke) .plane true 2)
    (hpair : LevelThreeOldformClasses D hecke hhecke .plane true) :
    CoordinateRankLowerBound D hecke hhecke .plane true :=
  coordinateRankLowerBound_goodPlane_of_period hodd
    (TernaryPeriodPolynomials.PeriodLink.levelThreePeriodNonvanishing n)
    D hecke hhecke hχ hbound hpair

end TernaryPeriodPolynomials.LevelThreeSource
