module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Oldform.Main
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Source.Odd

@[expose] public section


/-!
# The oldform classes at the level-three cusps, every character

For a nontrivial character and a nonzero pair the local joint eigenspaces at both level-three cusps
vanish (`levelThreeVanishing_of_nontrivial`, from SC's odd vanishing), so the
dimension-two hypothesis of `LevelThreeOldformClasses` cannot hold.  For the trivial character
`Main.lean` applies.  Hence `LevelThreeOldformClasses` at the good plane and at the bad line, for
every character, from the trivial-character inputs (R) and (L°) alone.

* `levelThreeOldformClasses_goodPlane`, `levelThreeOldformClasses_badLine`.

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

/-- A vanishing local joint eigenspace makes `LevelThreeOldformClasses` vacuous. -/
theorem levelThreeOldformClasses_of_localJoint_eq_bot (D : InducingData n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke) (side : Side)
    (good : Bool)
    (h : associatePair D ≠ ⊥ →
      localJoint n D.chi (pairCharacter D hecke hhecke) side good = ⊥) :
    LevelThreeOldformClasses D hecke hhecke side good := by
  intro hne _ h2
  rw [h hne, finrank_bot] at h2
  exact absurd h2 (by norm_num)

/-- **The oldform classes at the good plane, every character**, from (R) and (L°) for the trivial
character. -/
theorem levelThreeOldformClasses_goodPlane (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke)
    (hrank : LevelThreeRankTwoSpherical D hecke hhecke .plane true)
    (hL : SphericalLevelThreeSourceConstruction D .plane true) :
    LevelThreeOldformClasses D hecke hhecke .plane true := by
  by_cases hχ : D.chi = trivialCharacter
  · exact levelThreeOldformClasses_goodPlane_of_trivial D hecke hhecke hχ hrank hL
  · exact levelThreeOldformClasses_of_localJoint_eq_bot D hecke hhecke .plane true
      (fun hne => (levelThreeVanishing_of_nontrivial D hecke hhecke hχ hne).1)

/-- **The oldform classes at the bad line, every character**, from (R) and (L°) for the trivial
character. -/
theorem levelThreeOldformClasses_badLine (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke)
    (hrank : LevelThreeRankTwoSpherical D hecke hhecke .line false)
    (hL : SphericalLevelThreeSourceConstruction D .line false) :
    LevelThreeOldformClasses D hecke hhecke .line false := by
  by_cases hχ : D.chi = trivialCharacter
  · exact levelThreeOldformClasses_badLine_of_trivial D hecke hhecke hχ hrank hL
  · exact levelThreeOldformClasses_of_localJoint_eq_bot D hecke hhecke .line false
      (fun hne => (levelThreeVanishing_of_nontrivial D hecke hhecke hχ hne).2)

end TernaryPeriodPolynomials.Oldform
