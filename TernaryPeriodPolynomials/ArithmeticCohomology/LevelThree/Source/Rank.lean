module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Separation.Assembly
public import TernaryPeriodPolynomials.ArithmeticCohomology.Separation.SourceCoordinate

@[expose] public section


/-!
# Rank lower bounds for Shapiro coordinates

`CoordinateRankLowerBound D hecke hhecke side good` asks, for a nonzero pair with a
finite-dimensional local joint eigenspace, for as many linearly independent Shapiro coordinates of
summand classes as the dimension of that eigenspace.  This file proves the generic linear-algebra
steps used at the two level-three cusps:

* a vanishing local joint eigenspace gives the bound trivially
  (`coordinateRankLowerBound_of_localJoint_eq_bot`);
* `m` linearly independent vectors of any space `W` together with a linear map
  `Φ : W → sourceCocycles D side` whose composite with the Shapiro coordinate is injective give
  `CoordinateLowerBound D side good m` (`coordinateLowerBound_of_injective`);
* a dimension inequality `m ≤ finrank (coordinateImage D side good)` gives the bound directly
  (`coordinateLowerBound_of_le_finrank`), and the rank lower bound is equivalent to
  `finrank localJoint ≤ finrank coordinateImage` (`coordinateRankLowerBound_iff_finrank_le`).

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

/-- The empty family is a coordinate lower bound of length zero. -/
theorem coordinateLowerBound_zero (D : InducingData n) (side : Side) (good : Bool) :
    CoordinateLowerBound D side good 0 :=
  ⟨Fin.elim0, fun i => i.elim0, linearIndependent_empty_type⟩

/-- A vanishing local joint eigenspace makes the rank lower bound trivial. -/
theorem coordinateRankLowerBound_of_localJoint_eq_bot (D : InducingData n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke) (side : Side)
    (good : Bool)
    (h : associatePair D ≠ ⊥ →
      localJoint n D.chi (pairCharacter D hecke hhecke) side good = ⊥) :
    CoordinateRankLowerBound D hecke hhecke side good := by
  intro hne _
  have hzero : Module.finrank ℂ (localJoint n D.chi (pairCharacter D hecke hhecke) side good) =
      0 := by
    rw [h hne]
    exact finrank_bot ℂ _
  rw [hzero]
  exact coordinateLowerBound_zero D side good

/-- **Coordinate lower bound from an injective source construction.**  Linearly independent
vectors of a space `W`, pushed through a linear map into the source cocycles whose Shapiro
coordinate is injective, give as many linearly independent coordinates. -/
theorem coordinateLowerBound_of_injective {W : Type*} [AddCommGroup W] [Module ℂ W]
    (D : InducingData n) (side : Side) (good : Bool) (Φ : W →ₗ[ℂ] sourceCocycles D side)
    (hΦ : Function.Injective (sourceCoordinate D side good ∘ₗ Φ)) {m : ℕ} (v : Fin m → W)
    (hv : LinearIndependent ℂ v) : CoordinateLowerBound D side good m :=
  coordinateLowerBound_of_sources D side good m (fun i => Φ (v i))
    (hv.map' (sourceCoordinate D side good ∘ₗ Φ) (LinearMap.ker_eq_bot.mpr hΦ))

/-- A dimension inequality for the coordinate image gives the coordinate lower bound. -/
theorem coordinateLowerBound_of_le_finrank (D : InducingData n) (side : Side) (good : Bool)
    [FiniteDimensional ℂ (coordinateImage D side good)] {m : ℕ}
    (h : m ≤ Module.finrank ℂ (coordinateImage D side good)) :
    CoordinateLowerBound D side good m := by
  let b := Module.finBasis ℂ (coordinateImage D side good)
  refine ⟨fun i => ((b (Fin.castLE h i) : coordinateImage D side good) :
    CuspH2 n D.chi side good), fun i => (b (Fin.castLE h i)).2, ?_⟩
  exact (b.linearIndependent.comp _ (Fin.castLE_injective h)).map' (Submodule.subtype _)
    (Submodule.ker_subtype _)

/-- A coordinate lower bound is at most the dimension of the coordinate image. -/
theorem le_finrank_of_coordinateLowerBound (D : InducingData n) (side : Side) (good : Bool)
    [FiniteDimensional ℂ (coordinateImage D side good)] {m : ℕ}
    (h : CoordinateLowerBound D side good m) :
    m ≤ Module.finrank ℂ (coordinateImage D side good) := by
  obtain ⟨s, hs, hind⟩ := h
  let s' : Fin m → coordinateImage D side good := fun i => ⟨s i, hs i⟩
  have hind' : LinearIndependent ℂ s' :=
    LinearIndependent.of_comp (coordinateImage D side good).subtype hind
  simpa using hind'.fintype_card_le_finrank

/-- With a finite-dimensional local joint eigenspace, the rank lower bound is exactly the
dimension inequality `finrank localJoint ≤ finrank coordinateImage`. -/
theorem coordinateRankLowerBound_iff_finrank_le (D : InducingData n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke) (side : Side)
    (good : Bool) (hne : associatePair D ≠ ⊥)
    (hfin : FiniteDimensional ℂ (localJoint n D.chi (pairCharacter D hecke hhecke) side good)) :
    CoordinateRankLowerBound D hecke hhecke side good ↔
      Module.finrank ℂ (localJoint n D.chi (pairCharacter D hecke hhecke) side good) ≤
        Module.finrank ℂ (coordinateImage D side good) := by
  have hle := coordinateImage_le_localJoint D hecke hhecke side good
  have : FiniteDimensional ℂ (coordinateImage D side good) :=
    Submodule.finiteDimensional_of_le hle
  constructor
  · intro h
    exact le_finrank_of_coordinateLowerBound D side good (h hne hfin)
  · intro h _ _
    exact coordinateLowerBound_of_le_finrank D side good h

end TernaryPeriodPolynomials.LevelThreeSource
