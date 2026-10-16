module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Source.GoodPlaneFinal
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Even.Final

@[expose] public section


/-!
# The level-three inputs for the trivial character, split by parity

For `3 ≤ n` and `D.chi = trivialCharacter` the four level-three inputs `hfin3p`, `hfin3l`,
`hrank3p`, `hrank3l` of `eigenSeparated_of_openInputs` are obtained by splitting on the parity of
`n`:

* odd `n`: the good plane from `GoodPlaneFinal` (source realization from the level-three period
  nonvanishing) together with the local bound `2` and the oldform classes; the bad line
  from `Cases.lean` with the local bound, summand nonvanishing, the spherical bad-line source and
  the oldform classes.

The odd-degree inputs that are hypotheses are asked under `Odd n` only.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein
open TernaryPeriodPolynomials.SpectralSeparation
open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.Separation
open TernaryPeriodPolynomials.EvenLevelThree

namespace TernaryPeriodPolynomials.LevelThreeSource

variable {n : ℕ}

/-- **`hrank3p` for the trivial character.** -/
theorem coordinateRankLowerBound_goodPlane_trivial (hn : 3 ≤ n) (D : InducingData n)
    (hχ : D.chi = trivialCharacter) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke)
    (hbound : Odd n → associatePair D ≠ ⊥ →
      LocalUpperBound n D.chi (pairCharacter D hecke hhecke) .plane true 2)
    (hpair : Odd n → LevelThreeOldformClasses D hecke hhecke .plane true) :
    CoordinateRankLowerBound D hecke hhecke .plane true := by
  rcases Nat.even_or_odd n with heven | hodd
  · exact coordinateRankLowerBound_goodPlane_of_even D hecke hhecke hn heven
  · exact coordinateRankLowerBound_goodPlane_of_bound_oldform hodd D hecke hhecke hχ
      (hbound hodd) (hpair hodd)

/-- **`hrank3l` for the trivial character.** -/
theorem coordinateRankLowerBound_badLine_trivial (hn : 3 ≤ n) (D : InducingData n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke)
    (hbound : Odd n → associatePair D ≠ ⊥ →
      LocalUpperBound n D.chi (pairCharacter D hecke hhecke) .line false 2)
    (hS : Odd n → LevelThreeSummandNonvanishing D hecke hhecke .line false)
    (hN2L : Odd n → SphericalBadLineSource D)
    (hpair : Odd n → LevelThreeOldformClasses D hecke hhecke .line false) :
    CoordinateRankLowerBound D hecke hhecke .line false := by
  rcases Nat.even_or_odd n with heven | hodd
  · exact coordinateRankLowerBound_badLine_of_even D hecke hhecke hn heven
  · exact coordinateRankLowerBound_badLine_of_cases D hecke hhecke (hbound hodd) (hS hodd)
      (hN2L hodd) (hpair hodd)

/-- **`hfin3p` for the trivial character.** -/
theorem localJointFinite_goodPlane_trivial (hn : 3 ≤ n) (D : InducingData n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke)
    (hbound : Odd n → associatePair D ≠ ⊥ →
      LocalUpperBound n D.chi (pairCharacter D hecke hhecke) .plane true 2) :
    LocalJointFinite D hecke hhecke .plane true := by
  rcases Nat.even_or_odd n with heven | hodd
  · exact localJointFinite_goodPlane_of_even D hecke hhecke hn heven
  · exact fun hne => ⟨2, hbound hodd hne⟩

/-- **`hfin3l` for the trivial character.** -/
theorem localJointFinite_badLine_trivial (hn : 3 ≤ n) (D : InducingData n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke)
    (hbound : Odd n → associatePair D ≠ ⊥ →
      LocalUpperBound n D.chi (pairCharacter D hecke hhecke) .line false 2) :
    LocalJointFinite D hecke hhecke .line false := by
  rcases Nat.even_or_odd n with heven | hodd
  · exact localJointFinite_badLine_of_even D hecke hhecke hn heven
  · exact fun hne => ⟨2, hbound hodd hne⟩

end TernaryPeriodPolynomials.LevelThreeSource
