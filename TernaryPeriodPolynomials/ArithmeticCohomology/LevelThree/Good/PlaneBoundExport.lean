module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Good.PlaneBoundTwo
public import TernaryPeriodPolynomials.ArithmeticCohomology.Separation.Assembly

@[expose] public section


/-!
# The good-plane local upper bound `2` for the pair character

The form consumed by the rank lower bound: for a nonzero associate pair with trivial character and
`3 ≤ n`, the local joint generalized eigenspace of the pair character at the good plane of level
three has dimension at most `2`, given injectivity of the parity-projected level-three period
map (the Eichler–Shimura input of `LevelThreePeriodDimension`).

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.SpectralSeparation
open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.Spectral.CuspReduction

namespace TernaryPeriodPolynomials.LevelThree.GoodPlaneBoundExport

open TernaryPeriodPolynomials.Separation
open TernaryPeriodPolynomials.LevelThree.LevelThreePeriodParity (levelPeriodMap)

/-- **Local upper bound `2` at the good plane for the pair character** (`D.chi` trivial,
`3 ≤ n`, nonzero pair), given injectivity of the parity-projected period map. -/
theorem localUpperBound_goodPlane_two_of_trivial {n : ℕ} (hn : 3 ≤ n) (D : InducingData n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke)
    (hχ : D.chi = trivialCharacter) (hne : associatePair D ≠ ⊥)
    (hinj : Function.Injective (levelPeriodMap (n + 1) (-1))) :
    LocalUpperBound n D.chi (pairCharacter D hecke hhecke) .plane true 2 := by
  have hc := pairCharacter_two_sub_one_norm_le_of_trivial D hχ hecke hhecke hn hne
  have key := GoodPlaneBoundTwo.localUpperBound_two n (by omega)
    (pairCharacter D hecke hhecke) hc hinj
  rw [← hχ] at key
  exact key

end TernaryPeriodPolynomials.LevelThree.GoodPlaneBoundExport
