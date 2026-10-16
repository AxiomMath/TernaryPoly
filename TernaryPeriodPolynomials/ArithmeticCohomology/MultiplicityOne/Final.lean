module

public import TernaryPeriodPolynomials.ArithmeticCohomology.MultiplicityOne.MatchingFinal
public import TernaryPeriodPolynomials.ArithmeticCohomology.MultiplicityOne.NontrivialChi
public import TernaryPeriodPolynomials.ArithmeticCohomology.MultiplicityOne.BridgeMain

@[expose] public section


/-!
# The prime-three inputs for every character

Consumer form (`associatePair D ≠ ⊥`, `3 ≤ n`), every character: the nontrivial case is
`sphericalForcedByLocal_of_nontrivial`, the trivial case `sphericalForcedByLocal_of_bridge`,
with the level-three bridge `cohomological_exists_levelThree_classical`.
-/

noncomputable section

open GeneralEisenstein
open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.Separation

namespace TernaryPeriodPolynomials.MultiplicityOne

theorem sphericalForcedByLocal_of_pair (hbridge : LevelThreeBridge) {n : ℕ} (hn : 3 ≤ n)
    (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (hne : associatePair D ≠ ⊥) :
    SphericalForcedByLocal D hecke hhecke := by
  by_cases hχ : D.chi = trivialCharacter
  · exact sphericalForcedByLocal_of_bridge hbridge hn D hχ hecke hhecke hne
  · exact sphericalForcedByLocal_of_nontrivial D hχ hecke hhecke hne

theorem sphericalForcedByLocalLine_of_pair (hbridge : LevelThreeBridge) {n : ℕ} (hn : 3 ≤ n)
    (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (hne : associatePair D ≠ ⊥) :
    SphericalForcedByLocalLine D hecke hhecke := by
  by_cases hχ : D.chi = trivialCharacter
  · exact sphericalForcedByLocalLine_of_bridge hbridge hn D hχ hecke hhecke hne
  · exact sphericalForcedByLocalLine_of_nontrivial D hχ hecke hhecke hne

/-- **The level-three bridge.** -/
theorem levelThreeBridge : LevelThreeBridge :=
  fun σ _ hodd hcoh hlev => cohomological_exists_levelThree_classical σ hlev hodd hcoh

/-- **`SphericalForcedByLocal`, consumer form**: for `3 ≤ n` and a nonzero pair. -/
theorem sphericalForcedByLocal {n : ℕ} (hn : 3 ≤ n) (D : InducingData n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke)
    (hne : associatePair D ≠ ⊥) : SphericalForcedByLocal D hecke hhecke :=
  sphericalForcedByLocal_of_pair levelThreeBridge hn D hecke hhecke hne

/-- **`SphericalForcedByLocalLine`, consumer form**: for `3 ≤ n` and a nonzero pair. -/
theorem sphericalForcedByLocalLine {n : ℕ} (hn : 3 ≤ n) (D : InducingData n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke)
    (hne : associatePair D ≠ ⊥) : SphericalForcedByLocalLine D hecke hhecke :=
  sphericalForcedByLocalLine_of_pair levelThreeBridge hn D hecke hhecke hne

end TernaryPeriodPolynomials.MultiplicityOne
