module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Source.Rank
public import TernaryPeriodPolynomials.ArithmeticCohomology.Separation.SourceRealizationPlane
public import TernaryPeriodPolynomials.ArithmeticCohomology.Separation.SphericalBridge

@[expose] public section


/-!
# The rank lower bound by rank: one class, two classes

Workstream D bounds the local joint eigenspace at both level-three cusps by `2`.  This file splits
the rank lower bound accordingly:

* **rank `≤ 1`**: one source cocycle with nonzero coordinate suffices, i.e. E's
  `SourceRealization` (`coordinateRankLowerBound_of_cases`);
* **rank `2`** (the oldform pair of a level-one eigenform): two summand classes with independent
  coordinates, `LevelThreeOldformClasses`.

Source realization itself splits by the type of `D.cusp`:

* spherical `D`: the spherical source construction at the cusp (`SphericalGoodPlaneSource`, N2, and its bad-line analogue `SphericalBadLineSource`);
* non-spherical `D` (the newform case): the level-one cusp of the side sees nothing, so a nonzero
  summand of the side already has a nonzero coordinate at the level-three cusp
  (`coordinateImage_plane_true_ne_bot_of_nonspherical`,
  `coordinateImage_line_false_ne_bot_of_nonspherical`);
  what remains is the nonvanishing of the summand of the side, `LevelThreeSummandNonvanishing`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.SpectralSeparation
open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.SourceSpace
open TernaryPeriodPolynomials.Separation

namespace TernaryPeriodPolynomials.LevelThreeSource

variable {n : ℕ}

/-! ## Splitting by rank -/

/-- **Two classes in rank two.**  For a nonzero pair whose local joint eigenspace at the cusp is
two-dimensional, two summand classes with linearly independent coordinates. -/
def LevelThreeOldformClasses (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (side : Side) (good : Bool) : Prop :=
  associatePair D ≠ ⊥ →
    FiniteDimensional ℂ (localJoint n D.chi (pairCharacter D hecke hhecke) side good) →
      Module.finrank ℂ (localJoint n D.chi (pairCharacter D hecke hhecke) side good) = 2 →
        CoordinateLowerBound D side good 2

/-- One source with nonzero coordinate is a coordinate lower bound of length one. -/
theorem coordinateLowerBound_one (D : InducingData n) (side : Side) (good : Bool)
    (c : sourceCocycles D side) (hc : sourceCoordinate D side good c ≠ 0) :
    CoordinateLowerBound D side good 1 :=
  coordinateLowerBound_of_sources D side good 1 (fun _ => c)
    (linearIndependent_unique_iff.mpr hc)

/-- **The rank lower bound from the local bound `2`, source realization and the oldform
classes.** -/
theorem coordinateRankLowerBound_of_cases (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (side : Side) (good : Bool)
    (hbound : associatePair D ≠ ⊥ →
      LocalUpperBound n D.chi (pairCharacter D hecke hhecke) side good 2)
    (hreal : SourceRealization D hecke hhecke side good)
    (hpair : LevelThreeOldformClasses D hecke hhecke side good) :
    CoordinateRankLowerBound D hecke hhecke side good := by
  intro hne hfin
  have hle := (hbound hne).2
  rcases Nat.lt_or_ge
    (Module.finrank ℂ (localJoint n D.chi (pairCharacter D hecke hhecke) side good)) 2 with
      hlt | hge
  · have hle1 : Module.finrank ℂ
        (localJoint n D.chi (pairCharacter D hecke hhecke) side good) ≤ 1 := by omega
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle1 with h0 | h1
    · rw [h0]
      exact coordinateLowerBound_zero D side good
    · have hne' : localJoint n D.chi (pairCharacter D hecke hhecke) side good ≠ ⊥ := by
        intro hbot
        rw [hbot, finrank_bot] at h1
        exact zero_ne_one h1
      obtain ⟨c, hc⟩ := hreal hne'
      rw [h1]
      exact coordinateLowerBound_one D side good c hc
  · have h2 : Module.finrank ℂ (localJoint n D.chi (pairCharacter D hecke hhecke) side good) =
        2 := le_antisymm hle hge
    rw [h2]
    exact hpair hne hfin h2

/-! ## Splitting source realization by the type of `D.cusp` -/

/-- **The spherical source at the bad line** (bad-line analogue of N2). -/
def SphericalBadLineSource (D : InducingData n) : Prop :=
  SphericalCusp D.cusp → boundarySummand D .line ≠ ⊥ → coordinateImage D .line false ≠ ⊥

/-- **Summand nonvanishing at a level-three cusp.**  A nonzero local joint eigenspace at the cusp
of a nonzero pair forces the summand of the side to be nonzero. -/
def LevelThreeSummandNonvanishing (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (side : Side) (good : Bool) : Prop :=
  associatePair D ≠ ⊥ →
    localJoint n D.chi (pairCharacter D hecke hhecke) side good ≠ ⊥ → boundarySummand D side ≠ ⊥

/-- For a non-spherical `D` a nonzero line summand has a nonzero coordinate at the bad line. -/
theorem coordinateImage_line_false_ne_bot_of_nonspherical (D : InducingData n)
    (hns : ¬ SphericalCusp D.cusp) (hS : boundarySummand D .line ≠ ⊥) :
    coordinateImage D .line false ≠ ⊥ :=
  coordinateImage_ne_bot_of_other_eq_bot D .line false hS
    (coordinateImage_line_true_eq_bot_of_not_spherical D hns)

/-- **Source realization at the good plane** from summand nonvanishing and the spherical source
(N2). -/
theorem sourceRealization_goodPlane_of_cases (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (hne : associatePair D ≠ ⊥)
    (hS : LevelThreeSummandNonvanishing D hecke hhecke .plane true)
    (hN2 : SphericalGoodPlaneSource D) :
    SourceRealization D hecke hhecke .plane true := fun hloc => by
  have hsum := hS hne hloc
  refine (coordinateImage_ne_bot_iff D .plane true).mp ?_
  by_cases hsph : SphericalCusp D.cusp
  · exact hN2 hsph hsum
  · exact coordinateImage_plane_true_ne_bot_of_nonspherical D hsph hsum

/-- **Source realization at the bad line** from summand nonvanishing and the spherical source. -/
theorem sourceRealization_badLine_of_cases (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (hne : associatePair D ≠ ⊥)
    (hS : LevelThreeSummandNonvanishing D hecke hhecke .line false)
    (hN2L : SphericalBadLineSource D) :
    SourceRealization D hecke hhecke .line false := fun hloc => by
  have hsum := hS hne hloc
  refine (coordinateImage_ne_bot_iff D .line false).mp ?_
  by_cases hsph : SphericalCusp D.cusp
  · exact hN2L hsph hsum
  · exact coordinateImage_line_false_ne_bot_of_nonspherical D hsph hsum

/-- **Rank lower bound at the good plane** from D's bound, summand nonvanishing, the spherical
source (N2) and the oldform classes. -/
theorem coordinateRankLowerBound_goodPlane_of_cases (D : InducingData n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke)
    (hbound : associatePair D ≠ ⊥ →
      LocalUpperBound n D.chi (pairCharacter D hecke hhecke) .plane true 2)
    (hS : LevelThreeSummandNonvanishing D hecke hhecke .plane true)
    (hN2 : SphericalGoodPlaneSource D)
    (hpair : LevelThreeOldformClasses D hecke hhecke .plane true) :
    CoordinateRankLowerBound D hecke hhecke .plane true := fun hne =>
  coordinateRankLowerBound_of_cases D hecke hhecke .plane true hbound
    (sourceRealization_goodPlane_of_cases D hecke hhecke hne hS hN2) hpair hne

/-- **Rank lower bound at the bad line** from D's bound, summand nonvanishing, the spherical
source and the oldform classes. -/
theorem coordinateRankLowerBound_badLine_of_cases (D : InducingData n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke)
    (hbound : associatePair D ≠ ⊥ →
      LocalUpperBound n D.chi (pairCharacter D hecke hhecke) .line false 2)
    (hS : LevelThreeSummandNonvanishing D hecke hhecke .line false)
    (hN2L : SphericalBadLineSource D)
    (hpair : LevelThreeOldformClasses D hecke hhecke .line false) :
    CoordinateRankLowerBound D hecke hhecke .line false := fun hne =>
  coordinateRankLowerBound_of_cases D hecke hhecke .line false hbound
    (sourceRealization_badLine_of_cases D hecke hhecke hne hS hN2L) hpair hne

/-- The oldform classes are necessary for the rank lower bound. -/
theorem levelThreeOldformClasses_of_coordinateRankLowerBound (D : InducingData n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke) (side : Side)
    (good : Bool) (h : CoordinateRankLowerBound D hecke hhecke side good) :
    LevelThreeOldformClasses D hecke hhecke side good := by
  intro hne hfin h2
  have hb := h hne hfin
  rw [h2] at hb
  exact hb

end TernaryPeriodPolynomials.LevelThreeSource
