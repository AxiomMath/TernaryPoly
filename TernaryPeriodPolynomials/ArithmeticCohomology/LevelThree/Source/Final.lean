module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Source.Cases
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Source.Odd

@[expose] public section


/-!
# The rank lower bounds from trivial-character inputs

The inputs of `Cases.lean` are only needed for the trivial character: for every other character
the local joint eigenspaces at both level-three cusps vanish (`levelThreeVanishing_of_nontrivial`).
`coordinateRankLowerBound_goodPlane_final` and `coordinateRankLowerBound_badLine_final` take the
four inputs (local bound `2`, summand nonvanishing, spherical source, oldform classes) under
`D.chi = trivialCharacter` and deliver `hrank3p` and `hrank3l` of `eigenSeparated_of_openInputs`
for every `D`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.SpectralSeparation
open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.Separation

namespace TernaryPeriodPolynomials.LevelThreeSource

variable {n : ℕ}

/-- **`hrank3p` from trivial-character inputs.** -/
theorem coordinateRankLowerBound_goodPlane_final (D : InducingData n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke)
    (hbound : D.chi = trivialCharacter → associatePair D ≠ ⊥ →
      LocalUpperBound n D.chi (pairCharacter D hecke hhecke) .plane true 2)
    (hS : D.chi = trivialCharacter → LevelThreeSummandNonvanishing D hecke hhecke .plane true)
    (hN2 : D.chi = trivialCharacter → SphericalGoodPlaneSource D)
    (hpair : D.chi = trivialCharacter → LevelThreeOldformClasses D hecke hhecke .plane true) :
    CoordinateRankLowerBound D hecke hhecke .plane true := by
  by_cases hχ : D.chi = trivialCharacter
  · exact coordinateRankLowerBound_goodPlane_of_cases D hecke hhecke (hbound hχ) (hS hχ) (hN2 hχ)
      (hpair hχ)
  · exact coordinateRankLowerBound_of_localJoint_eq_bot D hecke hhecke .plane true
      fun hne => (levelThreeVanishing_of_nontrivial D hecke hhecke hχ hne).1

/-- **`hrank3l` from trivial-character inputs.** -/
theorem coordinateRankLowerBound_badLine_final (D : InducingData n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke)
    (hbound : D.chi = trivialCharacter → associatePair D ≠ ⊥ →
      LocalUpperBound n D.chi (pairCharacter D hecke hhecke) .line false 2)
    (hS : D.chi = trivialCharacter → LevelThreeSummandNonvanishing D hecke hhecke .line false)
    (hN2L : D.chi = trivialCharacter → SphericalBadLineSource D)
    (hpair : D.chi = trivialCharacter → LevelThreeOldformClasses D hecke hhecke .line false) :
    CoordinateRankLowerBound D hecke hhecke .line false := by
  by_cases hχ : D.chi = trivialCharacter
  · exact coordinateRankLowerBound_badLine_of_cases D hecke hhecke (hbound hχ) (hS hχ) (hN2L hχ)
      (hpair hχ)
  · exact coordinateRankLowerBound_of_localJoint_eq_bot D hecke hhecke .line false
      fun hne => (levelThreeVanishing_of_nontrivial D hecke hhecke hχ hne).2

/-- **Finiteness at the level-three cusps** (`hfin3p`, `hfin3l`) from the same local bound, for
every character. -/
theorem localJointFinite_final (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (side : Side) (good : Bool)
    (hbound : D.chi = trivialCharacter → associatePair D ≠ ⊥ →
      LocalUpperBound n D.chi (pairCharacter D hecke hhecke) side good 2)
    (hvan : D.chi ≠ trivialCharacter → associatePair D ≠ ⊥ →
      localJoint n D.chi (pairCharacter D hecke hhecke) side good = ⊥) :
    LocalJointFinite D hecke hhecke side good := by
  intro hne
  by_cases hχ : D.chi = trivialCharacter
  · exact ⟨2, hbound hχ hne⟩
  · exact LevelOneNontrivial.localJointFinite_of_eq_bot D hecke hhecke side good (hvan hχ hne) hne

/-- `hfin3p` from the trivial-character bound. -/
theorem localJointFinite_goodPlane_final (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke)
    (hbound : D.chi = trivialCharacter → associatePair D ≠ ⊥ →
      LocalUpperBound n D.chi (pairCharacter D hecke hhecke) .plane true 2) :
    LocalJointFinite D hecke hhecke .plane true :=
  localJointFinite_final D hecke hhecke .plane true hbound
    fun hχ hne => (levelThreeVanishing_of_nontrivial D hecke hhecke hχ hne).1

/-- `hfin3l` from the trivial-character bound. -/
theorem localJointFinite_badLine_final (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke)
    (hbound : D.chi = trivialCharacter → associatePair D ≠ ⊥ →
      LocalUpperBound n D.chi (pairCharacter D hecke hhecke) .line false 2) :
    LocalJointFinite D hecke hhecke .line false :=
  localJointFinite_final D hecke hhecke .line false hbound
    fun hχ hne => (levelThreeVanishing_of_nontrivial D hecke hhecke hχ hne).2

end TernaryPeriodPolynomials.LevelThreeSource
