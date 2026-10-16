module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.Level.OneNontrivial
public import TernaryPeriodPolynomials.ArithmeticCohomology.MultiplicityOne.Reduction

@[expose] public section


/-!
# The prime-three input for a nontrivial character

For a nontrivial character the Shapiro coordinate images at the two level-three cusps vanish
(`LevelOneNontrivial.coordinateImage_levelThree_eq_bot_of_nontrivial`). A nonzero pair has a source
cocycle with a nonzero coordinate at some cusp, so at a level-one cusp, and then `D.cusp` is
spherical. Hence both prime-three inputs hold outright for a nontrivial character and a nonzero
pair.
-/

noncomputable section

open GeneralEisenstein
open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.Separation

namespace TernaryPeriodPolynomials.MultiplicityOne

variable {n : ℕ}

/-- **A nonzero pair with a nontrivial character is spherical.** -/
theorem sphericalCusp_of_nontrivial (D : InducingData n) (hχ : D.chi ≠ trivialCharacter)
    (hne : associatePair D ≠ ⊥) : SphericalCusp D.cusp := by
  obtain ⟨side, good, c, hc⟩ := exists_sourceCoordinate_ne_zero D hne
  have hci : coordinateImage D side good ≠ ⊥ :=
    (coordinateImage_ne_bot_iff D side good).mpr ⟨c, hc⟩
  obtain ⟨hp, hl⟩ := LevelOneNontrivial.coordinateImage_levelThree_eq_bot_of_nontrivial D hχ
  cases side <;> cases good
  · exact sphericalCusp_of_coordinateImage_ne_bot D hci
  · exact absurd hp hci
  · exact absurd hl hci
  · exact sphericalCusp_of_coordinateImage_line_ne_bot D hci

theorem sphericalForcedByLocal_of_nontrivial (D : InducingData n)
    (hχ : D.chi ≠ trivialCharacter) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (hne : associatePair D ≠ ⊥) :
    SphericalForcedByLocal D hecke hhecke :=
  fun _ => sphericalCusp_of_nontrivial D hχ hne

theorem sphericalForcedByLocalLine_of_nontrivial (D : InducingData n)
    (hχ : D.chi ≠ trivialCharacter) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (hne : associatePair D ≠ ⊥) :
    SphericalForcedByLocalLine D hecke hhecke :=
  fun _ => sphericalCusp_of_nontrivial D hχ hne

end TernaryPeriodPolynomials.MultiplicityOne
