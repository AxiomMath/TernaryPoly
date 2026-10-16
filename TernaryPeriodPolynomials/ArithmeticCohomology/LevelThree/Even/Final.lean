module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Even.Vacuous
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Even.Bound
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Even.BadLineSummandWt
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Even.GoodPlaneSummandWt
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Source.Final
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Injective.Main

@[expose] public section


/-!
# The level-three rank lower bounds for even degree

For even `n` with `3 ≤ n` the four trivial-character inputs of CRL's
`coordinateRankLowerBound_{goodPlane,badLine}_final` are supplied:

* the local bound `2` (`Bound.lean`, from the bound `1` in odd weight);
* summand nonvanishing (`BadLineSummandWt.lean`, `GoodPlaneSummandWt.lean`, the weight-generic
  Eichler construction and period link);
* the spherical sources, vacuous because no cohomological representation of even degree is
  spherical (`Vacuous.lean`);
* the oldform classes (`Bound.lean`: a local joint eigenspace of dimension `2` does not occur).

The Eichler–Shimura injectivity of the parity-projected period maps is PI's
`levelPeriodMap_injective_goodPlane` / `levelPeriodMap_injective_badLine`.  The results hold for
every character: for `D.chi ≠ trivialCharacter` CRL's `levelThreeVanishing_of_nontrivial` applies.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.SpectralSeparation
open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.Separation
open TernaryPeriodPolynomials.LevelThreeSource
open TernaryPeriodPolynomials.LevelThreeInjective.Main
  (levelPeriodMap_injective_goodPlane levelPeriodMap_injective_badLine)

namespace TernaryPeriodPolynomials.EvenLevelThree

variable {n : ℕ}

/-- **Summand nonvanishing at the bad line for even degree**, unconditional (PI's injectivity). -/
theorem levelThreeSummandNonvanishing_badLine_even (D : InducingData n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke)
    (hn : 3 ≤ n) (heven : Even n) (hχ : D.chi = trivialCharacter) :
    LevelThreeSummandNonvanishing D hecke hhecke .line false :=
  levelThreeSummandNonvanishing_badLine_of_even D hecke hhecke hn heven hχ
    (levelPeriodMap_injective_badLine n)

/-- **Summand nonvanishing at the good plane for even degree**, unconditional. -/
theorem levelThreeSummandNonvanishing_goodPlane_even (D : InducingData n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke)
    (hn : 3 ≤ n) (heven : Even n) (hχ : D.chi = trivialCharacter) :
    LevelThreeSummandNonvanishing D hecke hhecke .plane true :=
  levelThreeSummandNonvanishing_goodPlane_of_even D hecke hhecke hn heven hχ
    (levelPeriodMap_injective_goodPlane n)

/-- **`hrank3p` for even degree.** -/
theorem coordinateRankLowerBound_goodPlane_of_even (D : InducingData n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke)
    (hn : 3 ≤ n) (heven : Even n) :
    CoordinateRankLowerBound D hecke hhecke .plane true :=
  coordinateRankLowerBound_goodPlane_final D hecke hhecke
    (fun hχ => levelThreeLocalUpperBound_two_of_even_goodPlane hn heven D hecke hhecke hχ
      (levelPeriodMap_injective_goodPlane n))
    (fun hχ => levelThreeSummandNonvanishing_goodPlane_of_even D hecke hhecke hn heven hχ
      (levelPeriodMap_injective_goodPlane n))
    (fun _ => sphericalGoodPlaneSource_of_even D heven)
    (fun hχ => levelThreeOldformClasses_goodPlane_of_even hn heven D hecke hhecke hχ
      (levelPeriodMap_injective_goodPlane n))

/-- **`hrank3l` for even degree.** -/
theorem coordinateRankLowerBound_badLine_of_even (D : InducingData n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke)
    (hn : 3 ≤ n) (heven : Even n) :
    CoordinateRankLowerBound D hecke hhecke .line false :=
  coordinateRankLowerBound_badLine_final D hecke hhecke
    (fun hχ => levelThreeLocalUpperBound_two_of_even_badLine hn heven D hecke hhecke hχ
      (levelPeriodMap_injective_badLine n))
    (fun hχ => levelThreeSummandNonvanishing_badLine_of_even D hecke hhecke hn heven hχ
      (levelPeriodMap_injective_badLine n))
    (fun _ => sphericalBadLineSource_of_even D heven)
    (fun hχ => levelThreeOldformClasses_badLine_of_even hn heven D hecke hhecke hχ
      (levelPeriodMap_injective_badLine n))

/-- **`hfin3p` for even degree.** -/
theorem localJointFinite_goodPlane_of_even (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (hn : 3 ≤ n) (heven : Even n) :
    LocalJointFinite D hecke hhecke .plane true :=
  localJointFinite_goodPlane_final D hecke hhecke
    (fun hχ => levelThreeLocalUpperBound_two_of_even_goodPlane hn heven D hecke hhecke hχ
      (levelPeriodMap_injective_goodPlane n))

/-- **`hfin3l` for even degree.** -/
theorem localJointFinite_badLine_of_even (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (hn : 3 ≤ n) (heven : Even n) :
    LocalJointFinite D hecke hhecke .line false :=
  localJointFinite_badLine_final D hecke hhecke
    (fun hχ => levelThreeLocalUpperBound_two_of_even_badLine hn heven D hecke hhecke hχ
      (levelPeriodMap_injective_badLine n))

end TernaryPeriodPolynomials.EvenLevelThree
