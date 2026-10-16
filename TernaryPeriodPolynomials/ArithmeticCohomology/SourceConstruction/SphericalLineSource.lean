module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Detect.LinePeriod
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Line.SourceFinal
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.SphericalPlaneSource

@[expose] public section


/-!
# The spherical line source construction for the trivial character

For `D.chi = 1` and a spherical `D`, the line source cocycle built from the sign-twisted Eichler
cocycle has nonzero Shapiro coordinate at the good line. This discharges the construction input
`SphericalSourceConstructionLine` of the separation argument for the trivial character, with no
hypothesis on the associate pair.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.Separation
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.SourceSpace

namespace TernaryPeriodPolynomials.SourceConstruction

variable {n : ℕ}

/-- **S1 at the good line for the trivial character.** -/
theorem sphericalSourceConstructionLine_of_trivial (D : InducingData n)
    (hchi : D.chi = trivialCharacter) : SphericalSourceConstructionLine D := fun hsph => by
  have odd : Odd n :=
    TernaryPeriodPolynomials.LevelOneCohomologicalParity.Helpers.cohomological_spherical_odd
      n D.cusp D.cohomological hsph
  obtain ⟨E, hE⟩ := lineSource_exists_cuspRes_goodLine_ne_zero D hsph hchi odd
  let c : sourceCocycles D .line :=
    ⟨lineSource D E, lineSource_isSourceCocycle D E (integral_character_trivial_of_eq D hchi)⟩
  refine (coordinateImage_ne_bot_iff D .line true).mpr ⟨c, ?_⟩
  rw [sourceCoordinate_apply]
  exact hE (evaluatedSource_realizes D .line c)

/-- The form consumed by the spectral targets. -/
theorem sphericalSourceConstructionLine_of_trivial_ne (D : InducingData n) :
    D.chi = trivialCharacter → associatePair D ≠ ⊥ → SphericalSourceConstructionLine D :=
  fun hchi _ => sphericalSourceConstructionLine_of_trivial D hchi

end TernaryPeriodPolynomials.SourceConstruction
