module

public import TernaryPeriodPolynomials.ArithmeticCohomology.RankTwo.Main
public import TernaryPeriodPolynomials.ArithmeticCohomology.Oldform.Main

@[expose] public section


/-!
# The rank-two input of the oldform classes, given the period injectivity

Workstream OLD's residual input (R) `LevelThreeRankTwoSpherical` at the good plane `(.plane, true)`
and at the bad line `(.line, false)`, for `3 ≤ n`, from `sphericalCusp_of_rankTwo_goodPlane` and
`sphericalCusp_of_rankTwo_badLine`, with the injectivity of the parity-projected period map as a
hypothesis.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein
open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.Oldform
open TernaryPeriodPolynomials.LevelThree.LevelThreePeriodParity (levelPeriodMap)

namespace TernaryPeriodPolynomials.RankTwo

variable {n : ℕ}

/-- **(R) at the good plane**, given injectivity of `levelPeriodMap (n + 1) (-1)`. -/
theorem levelThreeRankTwoSpherical_goodPlane_of_injective (hn : 3 ≤ n) (D : InducingData n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke)
    (hinj : Function.Injective (levelPeriodMap (n + 1) (-1))) :
    LevelThreeRankTwoSpherical D hecke hhecke .plane true :=
  fun hχ hne _ h2 => sphericalCusp_of_rankTwo_goodPlane hn D hecke hhecke hinj hχ hne h2

/-- **(R) at the bad line**, given injectivity of `levelPeriodMap (n + 1) 0`. -/
theorem levelThreeRankTwoSpherical_badLine_of_injective (hn : 3 ≤ n) (D : InducingData n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke)
    (hinj : Function.Injective (levelPeriodMap (n + 1) 0)) :
    LevelThreeRankTwoSpherical D hecke hhecke .line false :=
  fun hχ hne _ h2 => sphericalCusp_of_rankTwo_badLine hn D hecke hhecke hinj hχ hne h2

end TernaryPeriodPolynomials.RankTwo
