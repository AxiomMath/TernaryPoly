module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Oldform.GoodPlane
public import TernaryPeriodPolynomials.ArithmeticCohomology.PeriodLink.Final

@[expose] public section


/-!
# The oldform classes at the good plane, modulo rank-two sphericity only

The level-three period nonvanishing `LevelThreePeriodNonvanishing n` is `levelThreePeriodNonvanishing` (`PeriodLink.Final`).  Feeding it into `GoodPlane.lean`
leaves only the rank-two sphericity input (R) at the good plane.

* `levelThreeOldformClasses_goodPlane_of_rankTwo` (every character).

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

/-- **The oldform classes at the good plane, every character**, from (R) alone. -/
theorem levelThreeOldformClasses_goodPlane_of_rankTwo (D : InducingData n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke)
    (hrank : LevelThreeRankTwoSpherical D hecke hhecke .plane true) :
    LevelThreeOldformClasses D hecke hhecke .plane true :=
  levelThreeOldformClasses_goodPlane_of_period_all D hecke hhecke hrank
    (PeriodLink.levelThreePeriodNonvanishing n)

end TernaryPeriodPolynomials.Oldform
