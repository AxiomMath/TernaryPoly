module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Source.Inputs
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.Level.OneNontrivial

@[expose] public section


/-!
# The rank lower bounds at the good plane and the bad line

`coordinateRankLowerBound_goodPlane` and `coordinateRankLowerBound_badLine` deliver the inputs
`hrank3p` and `hrank3l` of `eigenSeparated_of_openInputs` from three inputs: local matching (U) and
source construction (L) of `Inputs.lean` for the trivial character, and for a nontrivial character
the vanishing `LevelThreeVanishing` (which is equivalent to the rank lower bound
there, `LevelOneNontrivial.levelThreeVanishing_iff_finite_rank`, because all Shapiro coordinates at
the level-three cusps vanish for such a character).  For the trivial character (U) gives linearly
independent level-three weight vectors and (L) pushes them injectively to Shapiro coordinates.

For the trivial character the vanishing input is void (`…_of_trivial`), and in odd degree (U)
reduces to the local bound `2`, the `LevelThreeBridge` and the oldform pair
(`coordinateRankLowerBound_of_bound`).  `eigenSeparated_of_levelThreeSourceInputs` is
`eigenSeparated_of_openInputs` with `hrank3p` and `hrank3l` replaced by these inputs.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.SpectralSeparation
open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.Spectral.LevelOneNontrivial (LevelThreeVanishing)
open TernaryPeriodPolynomials.Separation
open TernaryPeriodPolynomials.MultiplicityOne

namespace TernaryPeriodPolynomials.LevelThreeSource

variable {n : ℕ}

/-- **The rank lower bound at any cusp** from (U) and (L) for the trivial character and the
vanishing of the local joint eigenspace for a nontrivial one. -/
theorem coordinateRankLowerBound_of_inputs (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (side : Side) (good : Bool)
    (hU : LevelThreeLocalMatching D hecke hhecke side good)
    (hL : LevelThreeSourceConstruction D side good)
    (hO : D.chi ≠ trivialCharacter → associatePair D ≠ ⊥ →
      localJoint n D.chi (pairCharacter D hecke hhecke) side good = ⊥) :
    CoordinateRankLowerBound D hecke hhecke side good := by
  by_cases hχ : D.chi = trivialCharacter
  · intro hne hfin
    obtain ⟨v, hv⟩ := hU hχ hne hfin
    obtain ⟨Φ, hΦ⟩ := hL hχ hne
    exact coordinateLowerBound_of_injective D side good Φ hΦ v hv
  · exact coordinateRankLowerBound_of_localJoint_eq_bot D hecke hhecke side good (hO hχ)

/-- **Rank lower bound at the good plane** (`hrank3p` of `eigenSeparated_of_openInputs`). -/
theorem coordinateRankLowerBound_goodPlane (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke)
    (hU : LevelThreeLocalMatching D hecke hhecke .plane true)
    (hL : LevelThreeSourceConstruction D .plane true)
    (hvan : D.chi ≠ trivialCharacter → LevelThreeVanishing D hecke hhecke) :
    CoordinateRankLowerBound D hecke hhecke .plane true :=
  coordinateRankLowerBound_of_inputs D hecke hhecke .plane true hU hL
    fun hχ hne => (hvan hχ hne).1

/-- **Rank lower bound at the bad line** (`hrank3l` of `eigenSeparated_of_openInputs`). -/
theorem coordinateRankLowerBound_badLine (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke)
    (hU : LevelThreeLocalMatching D hecke hhecke .line false)
    (hL : LevelThreeSourceConstruction D .line false)
    (hvan : D.chi ≠ trivialCharacter → LevelThreeVanishing D hecke hhecke) :
    CoordinateRankLowerBound D hecke hhecke .line false :=
  coordinateRankLowerBound_of_inputs D hecke hhecke .line false hU hL
    fun hχ hne => (hvan hχ hne).2

/-- The good plane for the trivial character. -/
theorem coordinateRankLowerBound_goodPlane_of_trivial (D : InducingData n)
    (hχ : D.chi = trivialCharacter) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke)
    (hU : LevelThreeLocalMatching D hecke hhecke .plane true)
    (hL : LevelThreeSourceConstruction D .plane true) :
    CoordinateRankLowerBound D hecke hhecke .plane true :=
  coordinateRankLowerBound_goodPlane D hecke hhecke hU hL fun h => absurd hχ h

/-- The bad line for the trivial character. -/
theorem coordinateRankLowerBound_badLine_of_trivial (D : InducingData n)
    (hχ : D.chi = trivialCharacter) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke)
    (hU : LevelThreeLocalMatching D hecke hhecke .line false)
    (hL : LevelThreeSourceConstruction D .line false) :
    CoordinateRankLowerBound D hecke hhecke .line false :=
  coordinateRankLowerBound_badLine D hecke hhecke hU hL fun h => absurd hχ h

/-- The trivial character in odd degree: (U) from D's local bound `2`, M1's bridge and the oldform
pair. -/
theorem coordinateRankLowerBound_of_bound (hodd : Odd n) (hbridge : LevelThreeBridge)
    (D : InducingData n) (hχ : D.chi = trivialCharacter) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (side : Side) (good : Bool)
    (hbound : associatePair D ≠ ⊥ →
      LocalUpperBound n D.chi (pairCharacter D hecke hhecke) side good 2)
    (hpair : LevelThreeOldformPair D hecke hhecke side good)
    (hL : LevelThreeSourceConstruction D side good) :
    CoordinateRankLowerBound D hecke hhecke side good :=
  coordinateRankLowerBound_of_inputs D hecke hhecke side good
    (levelThreeLocalMatching_of_bound hodd hbridge D hecke hhecke side good hbound hpair) hL
    fun h => absurd hχ h

/-- **Eigencharacter separation with the level-three rank inputs replaced by (U), (L) and the
vanishing for a nontrivial character.** -/
theorem eigenSeparated_of_levelThreeSourceInputs (hn : 3 ≤ n) (D : InducingData n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke)
    (hloc1 : D.chi ≠ trivialCharacter → LevelOneLocalMultiplicityOne D hecke hhecke)
    (hS1 : D.chi ≠ trivialCharacter ∨ Odd n → associatePair D ≠ ⊥ →
      SphericalSourceConstruction D)
    (hS1L : D.chi ≠ trivialCharacter ∨ Odd n → associatePair D ≠ ⊥ →
      SphericalSourceConstructionLine D)
    (hS2 : D.chi ≠ trivialCharacter ∨ Odd n → associatePair D ≠ ⊥ →
      SphericalForcedByLocal D hecke hhecke)
    (hS2L : D.chi ≠ trivialCharacter ∨ Odd n → associatePair D ≠ ⊥ →
      SphericalForcedByLocalLine D hecke hhecke)
    (hfin3p : LocalJointFinite D hecke hhecke .plane true)
    (hfin3l : LocalJointFinite D hecke hhecke .line false)
    (hUp : LevelThreeLocalMatching D hecke hhecke .plane true)
    (hLp : LevelThreeSourceConstruction D .plane true)
    (hUl : LevelThreeLocalMatching D hecke hhecke .line false)
    (hLl : LevelThreeSourceConstruction D .line false)
    (hvan : D.chi ≠ trivialCharacter → LevelThreeVanishing D hecke hhecke) :
    EigenSeparated (awayThreeHeckeAlgebra D hecke) (associatePair D) :=
  eigenSeparated_of_openInputs hn D hecke hhecke hloc1 hS1 hS1L hS2 hS2L hfin3p hfin3l
    (coordinateRankLowerBound_goodPlane D hecke hhecke hUp hLp hvan)
    (coordinateRankLowerBound_badLine D hecke hhecke hUl hLl hvan)

end TernaryPeriodPolynomials.LevelThreeSource
