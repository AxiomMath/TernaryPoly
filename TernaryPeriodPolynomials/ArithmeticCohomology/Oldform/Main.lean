module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Oldform.Pair
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Source.Cases
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Source.Inputs

@[expose] public section


/-!
# The oldform classes at the level-three cusps (trivial character)

Workstream CRL reduces the rank lower bound at the two level-three cusps (good plane
`(.plane, true)`, bad line `(.line, false)`) to `LevelThreeOldformClasses`: when the local joint
eigenspace has dimension two, two summand classes with linearly independent Shapiro coordinates.
For the trivial character this follows from

* **(R) `LevelThreeRankTwoSpherical`**: a two-dimensional local joint eigenspace forces `D.cusp`
  to be spherical (strong multiplicity one at three: newforms of level three have one-dimensional
  eigenspaces, so a two-dimensional one is the oldform pair `f(τ)`, `f(3τ)` of a level-one form);
* **(L°) `SphericalLevelThreeSourceConstruction`**: for spherical `D`, a linear map from the
  level-three weight vectors to the source cocycles of the side with injective Shapiro coordinate
  at the cusp (CRL's `LevelThreeSourceConstruction` restricted to spherical `D`;
  `sphericalLevelThreeSourceConstruction_of_construction`);

together with the oldform pair proved here (`exists_oldformPair`): a spherical `D` has two
linearly independent level-three weight vectors, a spherical vector `v` and its Atkin–Lehner
translate.  Pushing them through (L°) gives the two classes.

* `levelThreeOldformClasses_of_trivial` (any cusp), `levelThreeOldformClasses_goodPlane_of_trivial`,
  `levelThreeOldformClasses_badLine_of_trivial`;
* `levelThreeOldformPair_of_rankTwoSpherical`: CRL's `LevelThreeOldformPair` from (R) alone;
* `levelThreeOldformClasses_of_matching`: the same conclusion from CRL's (U) and (L).

No bound on `n` is needed.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.SpectralSeparation
open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.SourceSpace
open TernaryPeriodPolynomials.Separation
open TernaryPeriodPolynomials.LevelThreeSource

namespace TernaryPeriodPolynomials.Oldform

variable {n : ℕ}

/-- **(R) Rank two forces sphericity.**  For the trivial character and a nonzero pair, a
two-dimensional local joint eigenspace at the cusp forces `D.cusp` to be spherical. -/
def LevelThreeRankTwoSpherical (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (side : Side) (good : Bool) : Prop :=
  D.chi = trivialCharacter → associatePair D ≠ ⊥ →
    FiniteDimensional ℂ (localJoint n D.chi (pairCharacter D hecke hhecke) side good) →
      Module.finrank ℂ (localJoint n D.chi (pairCharacter D hecke hhecke) side good) = 2 →
        SphericalCusp D.cusp

/-- **(L°) The level-three source construction for spherical `D`.**  For the trivial character,
a nonzero pair and spherical `D.cusp`, a linear map from the level-three weight vectors into the
source cocycles of the side whose Shapiro coordinate at the cusp is injective. -/
def SphericalLevelThreeSourceConstruction (D : InducingData n) (side : Side) (good : Bool) :
    Prop :=
  D.chi = trivialCharacter → associatePair D ≠ ⊥ → SphericalCusp D.cusp →
    ∃ Φ : levelThreeWeightVectors D.cusp (sourceWeight n) →ₗ[ℂ] sourceCocycles D side,
      Function.Injective (sourceCoordinate D side good ∘ₗ Φ)

/-- CRL's source construction (L) gives its spherical case (L°). -/
theorem sphericalLevelThreeSourceConstruction_of_construction (D : InducingData n) (side : Side)
    (good : Bool) (h : LevelThreeSourceConstruction D side good) :
    SphericalLevelThreeSourceConstruction D side good := fun hχ hne _ => h hχ hne

/-- **CRL's oldform pair input** from (R). -/
theorem levelThreeOldformPair_of_rankTwoSpherical (D : InducingData n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke) (side : Side)
    (good : Bool) (hrank : LevelThreeRankTwoSpherical D hecke hhecke side good) :
    LevelThreeOldformPair D hecke hhecke side good := fun hχ hne hfin h2 =>
  exists_oldformPair D (hrank hχ hne hfin h2)

/-- **The oldform classes for the trivial character** from (R) and (L°). -/
theorem levelThreeOldformClasses_of_trivial (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (side : Side) (good : Bool)
    (hχ : D.chi = trivialCharacter) (hrank : LevelThreeRankTwoSpherical D hecke hhecke side good)
    (hL : SphericalLevelThreeSourceConstruction D side good) :
    LevelThreeOldformClasses D hecke hhecke side good := by
  intro hne hfin h2
  have hsph := hrank hχ hne hfin h2
  obtain ⟨v, hv⟩ := exists_oldformPair D hsph
  obtain ⟨Φ, hΦ⟩ := hL hχ hne hsph
  exact coordinateLowerBound_of_injective D side good Φ hΦ v hv

/-- **The oldform classes at the good plane** (trivial character). -/
theorem levelThreeOldformClasses_goodPlane_of_trivial (D : InducingData n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke)
    (hχ : D.chi = trivialCharacter)
    (hrank : LevelThreeRankTwoSpherical D hecke hhecke .plane true)
    (hL : SphericalLevelThreeSourceConstruction D .plane true) :
    LevelThreeOldformClasses D hecke hhecke .plane true :=
  levelThreeOldformClasses_of_trivial D hecke hhecke .plane true hχ hrank hL

/-- **The oldform classes at the bad line** (trivial character). -/
theorem levelThreeOldformClasses_badLine_of_trivial (D : InducingData n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke)
    (hχ : D.chi = trivialCharacter)
    (hrank : LevelThreeRankTwoSpherical D hecke hhecke .line false)
    (hL : SphericalLevelThreeSourceConstruction D .line false) :
    LevelThreeOldformClasses D hecke hhecke .line false :=
  levelThreeOldformClasses_of_trivial D hecke hhecke .line false hχ hrank hL

/-- The oldform classes from CRL's local matching (U) and source construction (L). -/
theorem levelThreeOldformClasses_of_matching (D : InducingData n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke) (side : Side)
    (good : Bool) (hχ : D.chi = trivialCharacter)
    (hU : LevelThreeLocalMatching D hecke hhecke side good)
    (hL : LevelThreeSourceConstruction D side good) :
    LevelThreeOldformClasses D hecke hhecke side good := by
  intro hne hfin h2
  obtain ⟨v, hv⟩ := hU hχ hne hfin
  obtain ⟨Φ, hΦ⟩ := hL hχ hne
  have hb := coordinateLowerBound_of_injective D side good Φ hΦ v hv
  rw [h2] at hb
  exact hb

end TernaryPeriodPolynomials.Oldform
