module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Detect.BadLineSource
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Source.Cases

@[expose] public section


/-!
# The spherical bad-line source for the trivial character

`sphericalBadLineSource_of_trivial` is the bad-line analogue of N2: for the trivial character and
a spherical `D`, a nonzero line summand has a nonzero coordinate at the bad line.  It is the input
`SphericalBadLineSource` of the level-three rank lower bound.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein

namespace TernaryPeriodPolynomials.SourceConstruction

variable {n : ℕ}

/-- **The spherical source at the bad line, trivial character.** -/
theorem sphericalBadLineSource_of_trivial (D : InducingData n) (hchi : D.chi = trivialCharacter) :
    TernaryPeriodPolynomials.LevelThreeSource.SphericalBadLineSource D :=
  fun hsph _ =>
    (TernaryPeriodPolynomials.Separation.coordinateImage_ne_bot_iff D .line
      false).mpr (lineSourceConstruction_false_of_spherical D hchi hsph)

end TernaryPeriodPolynomials.SourceConstruction
