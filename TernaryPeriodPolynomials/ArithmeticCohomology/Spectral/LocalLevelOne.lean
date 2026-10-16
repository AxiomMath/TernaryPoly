module

public import TernaryPeriodPolynomials.EisensteinSeries.LevelOne.LocalMultiplicity
public import TernaryPeriodPolynomials.ArithmeticCohomology.Separation.LocalGlue

@[expose] public section


/-!
# Local uniqueness at the level-one cusps, in the interface forms

Delivery file for the two level-one cusps, the identity plane `(.plane, false)` and the good line
`(.line, true)`. It restates the local multiplicity results of
`LevelOneEisenstein.LocalMultiplicity` in the two interface forms:

* `LocalUpperBound n χ c side good 1` and `LocalMultiplicityOne n χ c side good` of the separation
  interface, for a trivial character `χ` and any character `c` with
  `‖c(T_2) - 1‖ ≤ 3/4`;
* `LocalUnique` of `LocalInterface` for the pair character of a paper datum with
  `3 ≤ n` and a nonzero associate pair (where the bound at `T_2` is automatic).

Original work by Claude Sonnet 5.5 and Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.SpectralSeparation
open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.Spectral.LocalInterface
open TernaryPeriodPolynomials.Separation

namespace TernaryPeriodPolynomials.Spectral.LocalLevelOne

variable {n : ℕ}

/-! ### The interface forms for a character `c` with `‖c(T_2) - 1‖ ≤ 3/4` -/

/-- Identity-plane cusp: `LocalUpperBound` with multiplicity one. -/
theorem identityPlane_localUpperBound (χ : RankOneCharacter) (hχ : χ = trivialCharacter)
    (hn : 0 < n) (c : HeckeCorrespondence → ℂ)
    (hc : ‖c (TpExistence.tp LocalUniqueness.two) - 1‖ ≤ 3 / 4) :
    LocalUpperBound n χ c .plane false 1 := by
  subst hχ
  exact LevelOneEisenstein.localJoint_identityPlane_finite_le_one hn c hc

/-- Good-line cusp: `LocalUpperBound` with multiplicity one. -/
theorem goodLine_localUpperBound (χ : RankOneCharacter) (hχ : χ = trivialCharacter)
    (hn : 0 < n) (c : HeckeCorrespondence → ℂ)
    (hc : ‖c (TpExistence.tp LocalUniqueness.two) - 1‖ ≤ 3 / 4) :
    LocalUpperBound n χ c .line true 1 := by
  subst hχ
  exact LevelOneEisenstein.localJoint_goodLine_finite_le_one hn c hc

/-- Identity-plane cusp: local multiplicity one. -/
theorem identityPlane_localMultiplicityOne (χ : RankOneCharacter) (hχ : χ = trivialCharacter)
    (hn : 0 < n) (c : HeckeCorrespondence → ℂ)
    (hc : ‖c (TpExistence.tp LocalUniqueness.two) - 1‖ ≤ 3 / 4) :
    LocalMultiplicityOne n χ c .plane false :=
  localMultiplicityOne_of_localUpperBound_one χ c .plane false
    (identityPlane_localUpperBound χ hχ hn c hc)

/-- Good-line cusp: local multiplicity one. -/
theorem goodLine_localMultiplicityOne (χ : RankOneCharacter) (hχ : χ = trivialCharacter)
    (hn : 0 < n) (c : HeckeCorrespondence → ℂ)
    (hc : ‖c (TpExistence.tp LocalUniqueness.two) - 1‖ ≤ 3 / 4) :
    LocalMultiplicityOne n χ c .line true :=
  localMultiplicityOne_of_localUpperBound_one χ c .line true
    (goodLine_localUpperBound χ hχ hn c hc)

/-! ### The pair character of a paper datum -/

/-- **Local uniqueness at the identity plane** for the pair character of a paper datum. -/
theorem identityPlane_localUnique (D : CohomologicalCuspData n)
    (hecke : BoundaryHecke n D.inducingData.chi)
    (hhecke : ActualBoundaryHecke n D.inducingData.chi hecke) (hn : 3 ≤ n)
    (hne : associatePair D.inducingData ≠ ⊥) :
    LocalUnique D.inducingData hecke hhecke .plane false :=
  (LevelOneEisenstein.localJoint_identityPlane_finite_le_one (by omega) _
    (LocalUniqueness.pairCharacter_two_sub_one_norm_le D hecke hhecke hn hne)).2

/-- **Local uniqueness at the good line** for the pair character of a paper datum. -/
theorem goodLine_localUnique (D : CohomologicalCuspData n)
    (hecke : BoundaryHecke n D.inducingData.chi)
    (hhecke : ActualBoundaryHecke n D.inducingData.chi hecke) (hn : 3 ≤ n)
    (hne : associatePair D.inducingData ≠ ⊥) :
    LocalUnique D.inducingData hecke hhecke .line true :=
  (LevelOneEisenstein.localJoint_goodLine_finite_le_one (by omega) _
    (LocalUniqueness.pairCharacter_two_sub_one_norm_le D hecke hhecke hn hne)).2

/-- The `LocalUpperBound` form for the pair character at the identity plane. -/
theorem identityPlane_localUpperBound_pair (D : CohomologicalCuspData n)
    (hecke : BoundaryHecke n D.inducingData.chi)
    (hhecke : ActualBoundaryHecke n D.inducingData.chi hecke) (hn : 3 ≤ n)
    (hne : associatePair D.inducingData ≠ ⊥) :
    LocalUpperBound n D.inducingData.chi (pairCharacter D.inducingData hecke hhecke) .plane false 1 :=
  LevelOneEisenstein.localJoint_identityPlane_finite_le_one (by omega) _
    (LocalUniqueness.pairCharacter_two_sub_one_norm_le D hecke hhecke hn hne)

/-- The `LocalUpperBound` form for the pair character at the good line. -/
theorem goodLine_localUpperBound_pair (D : CohomologicalCuspData n)
    (hecke : BoundaryHecke n D.inducingData.chi)
    (hhecke : ActualBoundaryHecke n D.inducingData.chi hecke) (hn : 3 ≤ n)
    (hne : associatePair D.inducingData ≠ ⊥) :
    LocalUpperBound n D.inducingData.chi (pairCharacter D.inducingData hecke hhecke) .line true 1 :=
  LevelOneEisenstein.localJoint_goodLine_finite_le_one (by omega) _
    (LocalUniqueness.pairCharacter_two_sub_one_norm_le D hecke hhecke hn hne)

end TernaryPeriodPolynomials.Spectral.LocalLevelOne
