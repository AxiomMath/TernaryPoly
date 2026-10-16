module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Source.Main
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Odd.Vanish

@[expose] public section


/-!
# The nontrivial characters at the level-three cusps

A nonzero pair forces the conductor of `χ` to divide three
 (`conductorThree_of_associatePair_ne_bot`), so a nontrivial `χ` with a nonzero pair
is odd, `χ(-1_∞) = -1` (`chi_realNegOne_eq_neg_one`), and for odd `χ` the local joint eigenspaces at
the good plane and the bad line vanish (`localJoint_plane_true_eq_bot`, `localJoint_line_false_eq_bot`).
This discharges the vanishing input of `Main.lean`: the rank lower bounds at the two level-three
cusps follow from local matching (U) and source construction (L) for the trivial character alone.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.SpectralSeparation
open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.Spectral.LevelOneNontrivial
  (LevelThreeVanishing conductorThree_of_associatePair_ne_bot chi_realNegOne_eq_neg_one)
open TernaryPeriodPolynomials.Separation

namespace TernaryPeriodPolynomials.LevelThreeSource

variable {n : ℕ}

/-- **The level-three vanishing for every nontrivial character.** -/
theorem levelThreeVanishing_of_nontrivial (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (hχ : D.chi ≠ trivialCharacter) :
    LevelThreeVanishing D hecke hhecke := by
  intro hne
  have hodd := chi_realNegOne_eq_neg_one hχ (conductorThree_of_associatePair_ne_bot D hne)
  exact ⟨TernaryPeriodPolynomials.SourceConstruction.localJoint_plane_true_eq_bot
      n D.chi hodd _,
    TernaryPeriodPolynomials.SourceConstruction.localJoint_line_false_eq_bot
      n D.chi hodd _⟩

/-- **Rank lower bound at the good plane, every character**, from (U) and (L) at the good plane. -/
theorem coordinateRankLowerBound_goodPlane_of_UL (D : InducingData n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke)
    (hU : LevelThreeLocalMatching D hecke hhecke .plane true)
    (hL : LevelThreeSourceConstruction D .plane true) :
    CoordinateRankLowerBound D hecke hhecke .plane true :=
  coordinateRankLowerBound_goodPlane D hecke hhecke hU hL
    (levelThreeVanishing_of_nontrivial D hecke hhecke)

/-- **Rank lower bound at the bad line, every character**, from (U) and (L) at the bad line. -/
theorem coordinateRankLowerBound_badLine_of_UL (D : InducingData n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke)
    (hU : LevelThreeLocalMatching D hecke hhecke .line false)
    (hL : LevelThreeSourceConstruction D .line false) :
    CoordinateRankLowerBound D hecke hhecke .line false :=
  coordinateRankLowerBound_badLine D hecke hhecke hU hL
    (levelThreeVanishing_of_nontrivial D hecke hhecke)

end TernaryPeriodPolynomials.LevelThreeSource
