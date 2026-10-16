module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Separation.Interface

@[expose] public section


/-!
# Global half: Shapiro coordinates of source classes

The Shapiro coordinate at a cusp of the class of an evaluated source cocycle is the class of the
restricted cocycle whose values are the source values at the inverse of a representative of the
cusp. Consequently a source whose values vanish at that adelic point has zero coordinate there
(`cuspRes_classOf_eq_zero_of_vanish`): this is the support half of `GlobalLowerBound`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.Spectral.CuspOrbits

namespace TernaryPeriodPolynomials.Separation

variable {n : ℕ}

/-- The Shapiro coordinate of a class is the class of the cocycle restricted to the cusp. -/
theorem cuspRes_classOf (χ : RankOneCharacter) (side : Side) (good : Bool)
    (z : cocycles rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) side)) :
    cuspRes n χ side good
        (classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) side) z) =
      classOf (cuspLevel side good) (rationalCoefficientComponent n χ)
        (fixedPointCycle rationalLevel (rationalCoefficientComponent n χ)
          (cuspFlag side good) z) :=
  fixedPointH2_classOf rationalLevel (rationalCoefficientComponent n χ) (cuspFlag side good) z

/-- Values of the restricted cocycle of an evaluated source. -/
theorem fixedPointCycle_evaluates (D : InducingData n) (side : Side)
    {c : (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly n}
    {z : cocycles rationalLevel (flagRepresentation (rationalCoefficientComponent n D.chi) side)}
    (hz : Evaluates D side c z) (q : RationalGL3) (x : Fin 3 → RationalGL3) :
    (fixedPointCycle rationalLevel (rationalCoefficientComponent n D.chi)
        (QuotientGroup.mk q : Flags side) z).val.val x =
      c (fun i => Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (x i)) (rationalGroup q⁻¹) :=
  hz x q

/-- **Support lemma.** If a source vanishes at the inverse of a representative of the reference
flag of a cusp, for all rational vertices, the class has zero Shapiro coordinate at that cusp. -/
theorem cuspRes_classOf_eq_zero_of_vanish (D : InducingData n) (side : Side) (good : Bool)
    {c : (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly n}
    {z : cocycles rationalLevel (flagRepresentation (rationalCoefficientComponent n D.chi) side)}
    (hz : Evaluates D side c z) (q : RationalGL3)
    (hq : (QuotientGroup.mk q : Flags side) = cuspFlag side good)
    (hv : ∀ x : Fin 3 → RationalGL3,
      c (fun i => Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (x i)) (rationalGroup q⁻¹) = 0) :
    cuspRes n D.chi side good
        (classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n D.chi) side) z) =
      0 := by
  rw [cuspRes_classOf]
  have hzero : fixedPointCycle rationalLevel (rationalCoefficientComponent n D.chi)
      (cuspFlag side good) z = 0 := by
    apply Subtype.ext
    apply Subtype.ext
    funext x
    rw [← hq, fixedPointCycle_evaluates D side hz q x, hv x]
    rfl
  rw [hzero, map_zero]

/-- A cusp whose local joint generalized eigenspace vanishes needs no global input. -/
theorem cuspStatement_of_localJoint_eq_bot (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (side : Side) (good : Bool)
    (h : localJoint n D.chi (pairCharacter D hecke hhecke) side good = ⊥) :
    CuspStatement D hecke hhecke side good := by
  rw [cuspStatement_iff, h]
  exact bot_le

theorem globalLowerBound_zero (D : InducingData n) (side : Side) (good : Bool) :
    GlobalLowerBound D side good 0 :=
  ⟨Fin.elim0, fun i => i.elim0, linearIndependent_empty_type⟩

theorem globalNonvanishing_of_localJoint_eq_bot (D : InducingData n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke) (side : Side)
    (good : Bool) (h : localJoint n D.chi (pairCharacter D hecke hhecke) side good = ⊥) :
    GlobalNonvanishing D hecke hhecke side good := fun hne => (hne h).elim

/-- A summand class supported at a cusp lies in the supported image. -/
theorem mem_supportedImage (D : InducingData n) (side : Side) (good : Bool)
    {a : StratumH2 n D.chi side} (ha : a ∈ boundarySummand D side)
    (hother : cuspRes n D.chi side (!good) a = 0) :
    cuspRes n D.chi side good a ∈ supportedImage D side good :=
  ⟨a, ⟨ha, hother⟩, rfl⟩

/-- The class of an evaluated source lies in the summand. -/
theorem classOf_mem_boundarySummand (D : InducingData n) (side : Side)
    {c : (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly n} (hc : IsSourceCocycle D side c)
    {z : cocycles rationalLevel (flagRepresentation (rationalCoefficientComponent n D.chi) side)}
    (hz : Evaluates D side c z) :
    classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n D.chi) side) z ∈
      boundarySummand D side :=
  Submodule.subset_span ⟨c, hc, z, hz, rfl⟩

end TernaryPeriodPolynomials.Separation
