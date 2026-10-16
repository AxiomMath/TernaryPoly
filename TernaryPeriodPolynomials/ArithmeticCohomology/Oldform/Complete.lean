module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Oldform.GoodPlaneFinal
public import TernaryPeriodPolynomials.ArithmeticCohomology.RankTwo.Final
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.BadLineSummandSource
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Injective.Main

@[expose] public section


/-!
# The oldform classes at both level-three cusps, assembled

Rank-two sphericity (R) at both level-three cusps is `levelThreeRankTwoSpherical_goodPlane_of_trivial` / `levelThreeRankTwoSpherical_badLine_of_trivial`
(`RankTwo.Final`, for `3 ≤ n`).  Hence:

* `levelThreeOldformClasses_goodPlane_complete` (`3 ≤ n`, every character): no further input;
* `levelThreeOldformClasses_badLine_complete` (`3 ≤ n`, every character): from the spherical
  level-three source construction at the bad line (L°);
* `sphericalLevelThreeSourceConstruction_badLine`: (L°) at the bad line, from `levelThreeSourceConstruction_badLine_of_period` with the injectivity
  `levelPeriodMap_injective_badLine`; the odd degree it needs comes from sphericity
  (`odd_of_sphericalCusp`);
* `levelThreeOldformClasses_badLine_complete'` (`3 ≤ n`, every character): no further input.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.SpectralSeparation
open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.Separation
open TernaryPeriodPolynomials.LevelThreeSource

namespace TernaryPeriodPolynomials.Oldform

variable {n : ℕ}

/-- **The oldform classes at the good plane**, every character, `3 ≤ n`. -/
theorem levelThreeOldformClasses_goodPlane_complete (hn : 3 ≤ n) (D : InducingData n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke) :
    LevelThreeOldformClasses D hecke hhecke .plane true :=
  levelThreeOldformClasses_goodPlane_of_rankTwo D hecke hhecke
    (RankTwo.levelThreeRankTwoSpherical_goodPlane_of_trivial hn D hecke hhecke)

/-- **The oldform classes at the bad line**, every character, `3 ≤ n`, from the spherical
level-three source construction at the bad line. -/
theorem levelThreeOldformClasses_badLine_complete (hn : 3 ≤ n) (D : InducingData n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke)
    (hL : SphericalLevelThreeSourceConstruction D .line false) :
    LevelThreeOldformClasses D hecke hhecke .line false :=
  levelThreeOldformClasses_badLine D hecke hhecke
    (RankTwo.levelThreeRankTwoSpherical_badLine_of_trivial hn D hecke hhecke) hL

/-- **(L°) at the bad line**: SC's level-three bad-line source construction, with PI's injectivity
of the parity-projected period map; a spherical cusp has odd degree. -/
theorem sphericalLevelThreeSourceConstruction_badLine (D : InducingData n) :
    SphericalLevelThreeSourceConstruction D .line false := fun hχ hne hsph =>
  sphericalLevelThreeSourceConstruction_of_construction D .line false
    (SourceConstruction.levelThreeSourceConstruction_badLine_of_period D
      (odd_of_sphericalCusp hsph D.cohomological)
      (LevelThreeInjective.Main.levelPeriodMap_injective_badLine n)) hχ hne hsph

/-- **The oldform classes at the bad line**, every character, `3 ≤ n`, with no further input. -/
theorem levelThreeOldformClasses_badLine_complete' (hn : 3 ≤ n) (D : InducingData n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke) :
    LevelThreeOldformClasses D hecke hhecke .line false :=
  levelThreeOldformClasses_badLine_complete hn D hecke hhecke
    (sphericalLevelThreeSourceConstruction_badLine D)

end TernaryPeriodPolynomials.Oldform
