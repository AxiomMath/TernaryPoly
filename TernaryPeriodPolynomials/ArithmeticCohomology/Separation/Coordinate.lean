module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Separation.Interface

@[expose] public section


/-!
# Coordinate statements: removing the support condition by cutoff

The cusp statement of `eigenSeparated_of_cusps` asks for a summand class with prescribed coordinate
at the cusp `(side, good)` AND vanishing coordinate at the other cusp of the side.  If the summand
is closed under cutting a class off to one cusp (`HasCutoff`, proved by multiplying the source
cocycles by the indicator of an orbit type at the place three), the support condition is free and
only the *coordinate statement* remains: every local joint eigenclass is the cusp coordinate of some
summand class.  The global lower bound then only asks for `m` linearly independent coordinates of
summand classes (`CoordinateLowerBound`).

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.SpectralSeparation
open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.Spectral.CuspReduction

namespace TernaryPeriodPolynomials.Separation

variable {n : ℕ}

/-- The summand can be cut off to one cusp: any class has a summand class with the same coordinate
at `(side, good)` and zero coordinate at the other cusp. -/
def HasCutoff (D : InducingData n) (side : Side) (good : Bool) : Prop :=
  ∀ a ∈ boundarySummand D side, ∃ a' ∈ boundarySummand D side,
    cuspRes n D.chi side good a' = cuspRes n D.chi side good a ∧
      cuspRes n D.chi side (!good) a' = 0

/-- The Shapiro coordinates at `(side, good)` of all summand classes. -/
def coordinateImage (D : InducingData n) (side : Side) (good : Bool) :
    Submodule ℂ (CuspH2 n D.chi side good) :=
  (boundarySummand D side).map (cuspRes n D.chi side good)

/-- **Coordinate statement.** Every local joint generalized eigenclass of the pair character is the
Shapiro coordinate of a summand class. -/
def CoordinateStatement (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (side : Side) (good : Bool) : Prop :=
  localJoint n D.chi (pairCharacter D hecke hhecke) side good ≤ coordinateImage D side good

/-- **Coordinate lower bound.** `m` summand classes with linearly independent coordinates at the
cusp. -/
def CoordinateLowerBound (D : InducingData n) (side : Side) (good : Bool) (m : ℕ) : Prop :=
  ∃ s : Fin m → CuspH2 n D.chi side good,
    (∀ i, s i ∈ coordinateImage D side good) ∧ LinearIndependent ℂ s

theorem supportedImage_le_coordinateImage (D : InducingData n) (side : Side) (good : Bool) :
    supportedImage D side good ≤ coordinateImage D side good :=
  Submodule.map_mono inf_le_left

/-- With cutoff, the coordinate image is the supported image. -/
theorem coordinateImage_le_supportedImage (D : InducingData n) (side : Side) (good : Bool)
    (hcut : HasCutoff D side good) :
    coordinateImage D side good ≤ supportedImage D side good := by
  rintro _ ⟨a, ha, rfl⟩
  obtain ⟨a', ha', h1, h2⟩ := hcut a ha
  exact ⟨a', ⟨ha', h2⟩, h1⟩

theorem coordinateImage_eq_supportedImage (D : InducingData n) (side : Side) (good : Bool)
    (hcut : HasCutoff D side good) :
    coordinateImage D side good = supportedImage D side good :=
  le_antisymm (coordinateImage_le_supportedImage D side good hcut)
    (supportedImage_le_coordinateImage D side good)

theorem cuspStatement_of_coordinate (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (side : Side) (good : Bool)
    (hcut : HasCutoff D side good) (h : CoordinateStatement D hecke hhecke side good) :
    CuspStatement D hecke hhecke side good := by
  rw [cuspStatement_iff]
  exact h.trans (coordinateImage_le_supportedImage D side good hcut)

theorem coordinateStatement_of_bounds (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (side : Side) (good : Bool) (m : ℕ)
    (hloc : LocalUpperBound n D.chi (pairCharacter D hecke hhecke) side good m)
    (hglob : CoordinateLowerBound D side good m) (hcut : HasCutoff D side good) :
    CoordinateStatement D hecke hhecke side good := by
  have hs : GlobalLowerBound D side good m := by
    obtain ⟨s, hs, hind⟩ := hglob
    exact ⟨s, fun i => coordinateImage_le_supportedImage D side good hcut (hs i), hind⟩
  have := cuspStatement_of_bounds D hecke hhecke side good m hloc hs
  rw [cuspStatement_iff] at this
  exact this.trans (supportedImage_le_coordinateImage D side good)

theorem coordinateStatement_of_multiplicityOne (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (side : Side) (good : Bool)
    (hloc : LocalMultiplicityOne n D.chi (pairCharacter D hecke hhecke) side good)
    (hglob : localJoint n D.chi (pairCharacter D hecke hhecke) side good ≠ ⊥ →
      coordinateImage D side good ≠ ⊥) :
    CoordinateStatement D hecke hhecke side good := by
  intro y hy
  by_cases hbot : localJoint n D.chi (pairCharacter D hecke hhecke) side good = ⊥
  · rw [hbot, Submodule.mem_bot] at hy
    rw [hy]
    exact Submodule.zero_mem _
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (hglob hbot)
  have hxL : x ∈ localJoint n D.chi (pairCharacter D hecke hhecke) side good := by
    obtain ⟨a, ha, rfl⟩ := hx
    exact cuspRes_mem_localJoint_of_mem D hecke hhecke side good ha
  obtain ⟨z, rfl⟩ := hloc x hxL y hy hx0
  exact Submodule.smul_mem _ z hx

/-- **Separation from coordinate statements and cutoffs.** -/
theorem eigenSeparated_of_coordinateStatements (D : InducingData n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke)
    (hcut : ∀ side good, HasCutoff D side good)
    (hcoord : ∀ side good, CoordinateStatement D hecke hhecke side good) :
    EigenSeparated (awayThreeHeckeAlgebra D hecke) (associatePair D) :=
  eigenSeparated_of_cuspStatements D hecke hhecke fun side good =>
    cuspStatement_of_coordinate D hecke hhecke side good (hcut side good) (hcoord side good)

end TernaryPeriodPolynomials.Separation
