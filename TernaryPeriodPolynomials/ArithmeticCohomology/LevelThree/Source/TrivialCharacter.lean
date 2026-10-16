module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Source.Trivial
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Good.PlaneBoundExport
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Bad.LineUpper
public import TernaryPeriodPolynomials.ArithmeticCohomology.Oldform.Complete
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.BadLineSummand
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Detect.BadLineFinal
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Injective.Main

@[expose] public section


/-!
# The level-three inputs for the trivial character, unconditionally

For `3 ≤ n` and `D.chi = trivialCharacter`, the four level-three inputs `hfin3p`, `hfin3l`,
`hrank3p`, `hrank3l` of `eigenSeparated_of_openInputs` hold with no further hypothesis.  The
odd-degree inputs of `Trivial.lean` are supplied by:

* the local bound `2`: at the good plane `localUpperBound_goodPlane_two_of_trivial`,
  at the bad line `localUpperBound_badLine_two` (bad line) with the `T₂` bound of the
  pair character `pairCharacter_two_sub_one_norm_le_of_trivial`, both with the injectivity of the
  level-three period map (`levelPeriodMap_injective_goodPlane`, `levelPeriodMap_injective_badLine`);
* the oldform classes: `levelThreeOldformClasses_goodPlane_complete`,
  `levelThreeOldformClasses_badLine_complete'`;
* at the bad line, summand nonvanishing `levelThreeSummandNonvanishing_badLine_of_period` and the
  spherical source `sphericalBadLineSource_of_trivial`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein
open TernaryPeriodPolynomials.SpectralSeparation
open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.Separation
open TernaryPeriodPolynomials.LevelThreeInjective.Main
  (levelPeriodMap_injective_goodPlane levelPeriodMap_injective_badLine)
open TernaryPeriodPolynomials.LevelThree.GoodPlaneBoundExport
  (localUpperBound_goodPlane_two_of_trivial)
open TernaryPeriodPolynomials.LevelThree.BadLineUpper (localUpperBound_badLine_two)
open TernaryPeriodPolynomials.Oldform
  (levelThreeOldformClasses_goodPlane_complete levelThreeOldformClasses_badLine_complete')
open TernaryPeriodPolynomials.SourceConstruction
  (levelThreeSummandNonvanishing_badLine_of_period sphericalBadLineSource_of_trivial)

namespace TernaryPeriodPolynomials.LevelThreeSource

variable {n : ℕ}

/-- The local bound `2` at the good plane, trivial character. -/
theorem localUpperBound_goodPlane_trivial (hn : 3 ≤ n) (D : InducingData n)
    (hχ : D.chi = trivialCharacter) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (hne : associatePair D ≠ ⊥) :
    LocalUpperBound n D.chi (pairCharacter D hecke hhecke) .plane true 2 :=
  localUpperBound_goodPlane_two_of_trivial
    hn D hecke hhecke hχ hne (levelPeriodMap_injective_goodPlane n)

/-- The local bound `2` at the bad line, trivial character. -/
theorem localUpperBound_badLine_trivial (hn : 3 ≤ n) (D : InducingData n)
    (hχ : D.chi = trivialCharacter) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (hne : associatePair D ≠ ⊥) :
    LocalUpperBound n D.chi (pairCharacter D hecke hhecke) .line false 2 := by
  have key := localUpperBound_badLine_two n hn
      (pairCharacter D hecke hhecke)
      (pairCharacter_two_sub_one_norm_le_of_trivial D hχ hecke hhecke hn hne)
      (levelPeriodMap_injective_badLine n)
  rw [← hχ] at key
  exact key

/-- **`hfin3p`, trivial character, unconditionally.** -/
theorem localJointFinite_goodPlane (hn : 3 ≤ n) (D : InducingData n)
    (hχ : D.chi = trivialCharacter) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) :
    LocalJointFinite D hecke hhecke .plane true :=
  localJointFinite_goodPlane_trivial hn D hecke hhecke
    fun _ => localUpperBound_goodPlane_trivial hn D hχ hecke hhecke

/-- **`hfin3l`, trivial character, unconditionally.** -/
theorem localJointFinite_badLine_unconditional (hn : 3 ≤ n) (D : InducingData n)
    (hχ : D.chi = trivialCharacter) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) :
    LocalJointFinite D hecke hhecke .line false :=
  localJointFinite_badLine_trivial hn D hecke hhecke
    fun _ => localUpperBound_badLine_trivial hn D hχ hecke hhecke

/-- **`hrank3p`, trivial character, unconditionally.** -/
theorem coordinateRankLowerBound_goodPlane_unconditional (hn : 3 ≤ n) (D : InducingData n)
    (hχ : D.chi = trivialCharacter) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) :
    CoordinateRankLowerBound D hecke hhecke .plane true :=
  coordinateRankLowerBound_goodPlane_trivial hn D hχ hecke hhecke
    (fun _ => localUpperBound_goodPlane_trivial hn D hχ hecke hhecke)
    (fun _ => levelThreeOldformClasses_goodPlane_complete
      hn D hecke hhecke)

/-- **`hrank3l`, trivial character, unconditionally.** -/
theorem coordinateRankLowerBound_badLine_unconditional (hn : 3 ≤ n) (D : InducingData n)
    (hχ : D.chi = trivialCharacter) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) :
    CoordinateRankLowerBound D hecke hhecke .line false :=
  coordinateRankLowerBound_badLine_trivial hn D hecke hhecke
    (fun _ => localUpperBound_badLine_trivial hn D hχ hecke hhecke)
    (fun hodd =>
      levelThreeSummandNonvanishing_badLine_of_period
        D hecke hhecke hχ hodd (levelPeriodMap_injective_badLine n))
    (fun _ => sphericalBadLineSource_of_trivial
      D hχ)
    (fun _ => levelThreeOldformClasses_badLine_complete'
      hn D hecke hhecke)

end TernaryPeriodPolynomials.LevelThreeSource
