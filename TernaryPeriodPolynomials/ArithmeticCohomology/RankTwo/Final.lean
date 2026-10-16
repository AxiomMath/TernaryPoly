module

public import TernaryPeriodPolynomials.ArithmeticCohomology.RankTwo.Oldform
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Injective.Main

@[expose] public section


/-!
# The rank-two input of the oldform classes

Workstream OLD's residual input (R) `LevelThreeRankTwoSpherical` at the good plane `(.plane, true)`
and at the bad line `(.line, false)`, for `3 ≤ n` (the trivial character is part of the statement):
the period-injectivity hypotheses of `Oldform.lean` are discharged by `levelPeriodMap_injective_goodPlane` and `levelPeriodMap_injective_badLine`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein
open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.Oldform

namespace TernaryPeriodPolynomials.RankTwo

variable {n : ℕ}

/-- **(R) at the good plane**: for the trivial character, a nonzero pair and `3 ≤ n`, a
two-dimensional local joint eigenspace of the pair character at the good plane forces `D.cusp` to
be spherical. -/
theorem levelThreeRankTwoSpherical_goodPlane_of_trivial (hn : 3 ≤ n) (D : InducingData n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke) :
    LevelThreeRankTwoSpherical D hecke hhecke .plane true :=
  levelThreeRankTwoSpherical_goodPlane_of_injective hn D hecke hhecke
    (LevelThreeInjective.Main.levelPeriodMap_injective_goodPlane n)

/-- **(R) at the bad line**: for the trivial character, a nonzero pair and `3 ≤ n`, a
two-dimensional local joint eigenspace of the pair character at the bad line forces `D.cusp` to be
spherical. -/
theorem levelThreeRankTwoSpherical_badLine_of_trivial (hn : 3 ≤ n) (D : InducingData n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke) :
    LevelThreeRankTwoSpherical D hecke hhecke .line false :=
  levelThreeRankTwoSpherical_badLine_of_injective hn D hecke hhecke
    (LevelThreeInjective.Main.levelPeriodMap_injective_badLine n)

end TernaryPeriodPolynomials.RankTwo
