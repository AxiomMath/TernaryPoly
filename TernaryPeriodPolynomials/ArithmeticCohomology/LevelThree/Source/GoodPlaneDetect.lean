module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Source.GoodPlaneSourceCusp
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Source.Cases
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Detect.GoodPlaneGeneric

@[expose] public section


/-!
# Detection of the good-plane cell source

The good-plane cell source `goodPlaneSource D E` of a level-three Levi cocycle datum `E` has, at the
good-plane cusp point, the identity-plane cup value of `E.α` (`goodPlaneSource_rational_cusp`).
Workstream SC's generic good-plane detection (`cuspRes_plane_true_ne_zero_of_identityCup`,
`notCoboundary_of_period`) then makes its good-plane Shapiro coordinate nonzero as soon as the
level-three period class of `E` is nonzero:
```
LevelThreePeriodClass E : ¬ ∃ w, ∀ m ∈ Γ₁'(3), E.α m 1 = ρ(m) w - w   (Sym^{n+1} ⊗ det⁻¹)
```
The other hypothesis of `notCoboundary_of_period` (the Levi values do not see real translates by
`Γ₁'(3)`) follows from the level field of `E` (`alpha_atInfinity_level`).

Consequences, for the trivial character:
* `goodPlaneSource_sourceCoordinate_ne_zero`;
* `sourceRealization_goodPlane_of_period`: source realization at the good plane from a datum with
  nonzero period class;
* `levelThreeSummandNonvanishing_goodPlane_of_period`: the input `LevelThreeSummandNonvanishing` of
  `Cases.lean` at the good plane.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open Matrix GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.SpectralSeparation
open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.SourceSpace
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
  (binaryArithmeticLevel mem_binaryArithmeticLevel_iff)
open TernaryPeriodPolynomials.LevelThree.ParabolicBounds (levelRep)
open TernaryPeriodPolynomials.AnalyticClasses
  (realLeviMatrix finiteLeviMatrix rationalAdele_intMatrix map_integralEmbedding_intCast)
open TernaryPeriodPolynomials.SourceConstruction
  (PlaneLeviCocycle gpDelta gpMu notCoboundary_of_period cuspRes_plane_true_ne_zero_of_identityCup)
open TernaryPeriodPolynomials.MultiplicityOne (levelThreeValues)
open TernaryPeriodPolynomials.Separation

namespace TernaryPeriodPolynomials.LevelThreeSource

variable {n : ℕ}

/-! ## Levi values of a level-three datum do not see real translates by `Γ₁'(3)` -/

/-- An integral matrix of `Γ₁'(3)` lies in the level-three Levi level. -/
theorem planeLeviLevel_intCast {A : GeneralLinearGroup (Fin 2) ℤ}
    (hA : A ∈ binaryArithmeticLevel) :
    PlaneLeviLevel (GeneralLinearGroup.map (Int.castRingHom IntegralAdeles) A) := by
  have h := (mem_binaryArithmeticLevel_iff A).mp hA
  refine ⟨?_, ?_⟩
  · show integralReduction ((Int.castRingHom IntegralAdeles) (A.val 1 0)) = 0
    simpa using h 0
  · show integralReduction ((Int.castRingHom IntegralAdeles) (A.val 1 1)) = 1
    simpa using h 1

/-- A level-three vector does not see a real translate by `Γ₁'(3)`. -/
theorem realize_atInfinity_level (σ : CuspidalRepresentation) (v : σ.smooth)
    (hv : v.val ∈ levelThreeValues σ) {A : GeneralLinearGroup (Fin 2) ℤ}
    (hA : A ∈ binaryArithmeticLevel) :
    σ.realize v (atInfinity (GeneralLinearGroup.map (Int.castRingHom ℝ) A)) = σ.realize v 1 := by
  have fixed : (⟨σ.π (atFinite (finiteLeviMatrix A)) v.val, σ.smooth_stable _ _ v.property⟩ :
      σ.smooth) = v := by
    apply Subtype.ext
    change σ.π (atFinite (GeneralLinearGroup.map (Int.castRingHom FiniteAdeles) A)) v.val = v.val
    rw [← map_integralEmbedding_intCast]
    exact hv _ (planeLeviLevel_intCast hA)
  have key : ∀ point : BinaryAdelicGL,
      σ.realize v (point * atFinite (finiteLeviMatrix A)) = σ.realize v point := by
    intro point
    rw [← σ.equivariant, fixed]
  have h1 := key (atInfinity (realLeviMatrix A))
  rw [← rationalAdele_intMatrix A] at h1
  have h2 := σ.leftRational (GeneralLinearGroup.map (Int.castRingHom ℚ) A) v 1
  rw [mul_one] at h2
  exact h1.symm.trans h2

/-- **The Levi values of a level-three datum do not see real translates by `Γ₁'(3)`.** -/
theorem alpha_atInfinity_level {σ : CuspidalRepresentation} (E : LevelLeviCocycleData σ n)
    (h : BinaryRealGL) {A : GeneralLinearGroup (Fin 2) ℤ} (hA : A ∈ binaryArithmeticLevel) :
    E.α h (atInfinity (GeneralLinearGroup.map (Int.castRingHom ℝ) A)) = E.α h 1 := by
  apply Subtype.ext
  apply MvPolynomial.ext
  intro ν
  rw [← E.lift_realize ν h, ← E.lift_realize ν h]
  exact realize_atInfinity_level σ (E.lift ν h) (E.level ν h) hA

/-! ## Detection -/

/-- The Levi cocycle of a level-three datum, in SC's generic format. -/
def LevelLeviCocycleData.toPlaneLeviCocycle {σ : CuspidalRepresentation}
    (E : LevelLeviCocycleData σ n) : PlaneLeviCocycle n :=
  ⟨E.α, E.cocycle, E.orth⟩

/-- **The level-three period class of a datum is nonzero**: the restriction of the period cocycle
`m ↦ E.α m 1` to `Γ₁'(3)` is not a crossed coboundary of `Sym^{n+1} ⊗ det⁻¹`. -/
def LevelThreePeriodClass {σ : CuspidalRepresentation} (E : LevelLeviCocycleData σ n) : Prop :=
  ¬ ∃ w : Binary.HomogeneousPoly (n + 1), ∀ m : binaryArithmeticLevel,
    E.α (gpMu m) 1 = levelRep (n + 1) (-1) m w - w

/-- **The good-plane coordinate of the cell source is nonzero** when the period class is. -/
theorem goodPlaneSource_sourceCoordinate_ne_zero (D : InducingData n)
    (hχ : D.chi = trivialCharacter) (hn : 0 < n) (E : LevelLeviCocycleData D.cusp n)
    (hP : LevelThreePeriodClass E) :
    sourceCoordinate D .plane true
      ⟨goodPlaneSource D E, goodPlaneSource_isSourceCocycle_of_trivial D E hχ⟩ ≠ 0 := by
  have hint : ∀ u : IntegralAdelesˣ, D.chi.toMonoidHom (integralAdeleUnit u) = 1 := fun u => by
    rw [hχ]
    rfl
  have hN := notCoboundary_of_period E.toPlaneLeviCocycle
    (fun m => alpha_atInfinity_level E gpDelta m.property) hP
  show cuspRes n D.chi .plane true
    (classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n D.chi) .plane)
      (evaluatedSource D .plane
        ⟨goodPlaneSource D E, goodPlaneSource_isSourceCocycle_of_trivial D E hχ⟩)) ≠ 0
  exact cuspRes_plane_true_ne_zero_of_identityCup D hχ hn E.toPlaneLeviCocycle hN
    (evaluatedSource_realizes D .plane _) (fun x => goodPlaneSource_rational_cusp D E hint x)

/-- **Source realization at the good plane** from a level-three datum with nonzero period class
whenever the local joint eigenspace there is nonzero. -/
theorem sourceRealization_goodPlane_of_period (D : InducingData n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke)
    (hχ : D.chi = trivialCharacter) (hn : 0 < n)
    (hE : localJoint n D.chi (pairCharacter D hecke hhecke) .plane true ≠ ⊥ →
      ∃ E : LevelLeviCocycleData D.cusp n, LevelThreePeriodClass E) :
    SourceRealization D hecke hhecke .plane true := fun hloc => by
  obtain ⟨E, hP⟩ := hE hloc
  exact ⟨_, goodPlaneSource_sourceCoordinate_ne_zero D hχ hn E hP⟩

/-- **Summand nonvanishing at the good plane** (the input of `Cases.lean`) from a level-three datum
with nonzero period class. -/
theorem levelThreeSummandNonvanishing_goodPlane_of_period (D : InducingData n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke)
    (hχ : D.chi = trivialCharacter) (hn : 0 < n)
    (hE : associatePair D ≠ ⊥ →
      localJoint n D.chi (pairCharacter D hecke hhecke) .plane true ≠ ⊥ →
        ∃ E : LevelLeviCocycleData D.cusp n, LevelThreePeriodClass E) :
    LevelThreeSummandNonvanishing D hecke hhecke .plane true := by
  intro hne hloc hbot
  obtain ⟨c, hc⟩ := sourceRealization_goodPlane_of_period D hecke hhecke hχ hn (hE hne) hloc
  apply hc
  have hmem : sourceClass D .plane c ∈ boundarySummand D .plane := by
    rw [← sourceClass_range]
    exact LinearMap.mem_range_self _ c
  rw [hbot, Submodule.mem_bot] at hmem
  rw [sourceCoordinate_apply, hmem, map_zero]

end TernaryPeriodPolynomials.LevelThreeSource
