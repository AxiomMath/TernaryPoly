module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Source.LevelThreeEichlerLift
public import TernaryPeriodPolynomials.ArithmeticCohomology.MultiplicityOne.BridgeMain

@[expose] public section


/-!
# The level-three Eichler Levi cocycle datum

Headline of the level-three Eichler construction (the counterpart of SC's
`exists_eichlerCocycle_of_cohomological` + `LeviCocycleData`):

* `levelThreeEichlerData coh hσ halfWeight hw v hv : LevelLeviCocycleData σ n` — the datum built
  from a smooth level-three vector `v` of weight `-(n + 3)` (a member of
  `levelThreeClassicalVectors σ halfWeight`) in a cohomological cuspidal representation `σ`.  Its
  cocycle is the Eichler integral of the holomorphic form of `v`:
  `α A = ½ (Per(A i) + J Per(-conj(A i)))` realized as a function on `GL₂(𝔸)`
  (`levelThreeEichlerData_α` : `α = lteAlpha σ n halfWeight v`, with `lteAlpha` the realization
  `hilbertLift` of `lteCocycle`).
* `lteAlpha` is additive and homogeneous in the vector (`lteAlpha_add`, `lteAlpha_smul`), so the
  cocycles of the level-three weight vectors form a linear family (`lteFamilyMap`), which later
  detection arguments can use to identify the class of the cocycle of `v`.
* `exists_levelLeviCocycleData` : existence of the datum from a nonzero level-three weight
  vector; `exists_levelLeviCocycleData_of_levelThree` : existence from a nonzero level-three
  vector alone, in odd degree.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.LevelThreeSource

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.AnalyticClasses
open TernaryPeriodPolynomials.PlaneEisensteinContinuation
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.MultiplicityOne
  (LevelThreeCusp levelThreeValues levelThreeClassicalVectors
    cohomological_exists_levelThree_classical)

/-! ## Linearity in the vector -/

section Linear

variable (σ : CuspidalRepresentation) (n : ℕ)

theorem ltePotential_add (h : ℤ) (v v' : σ.H) (z : ℂ) (hz : 0 < z.im) :
    ltePotential σ n h (v + v') z = ltePotential σ n h v z + ltePotential σ n h v' z := by
  have hz' : 0 < (binaryComplexReflection z).im := by
    rw [binaryComplexReflection_im]
    exact hz
  unfold ltePotential
  rw [l3_period_add σ n h v v' z hz, l3_period_add σ n h v v' (binaryComplexReflection z) hz',
    map_add]
  module

theorem ltePotential_smul (h : ℤ) (c : ℂ) (v : σ.H) (z : ℂ) :
    ltePotential σ n h (c • v) z = c • ltePotential σ n h v z := by
  unfold ltePotential
  rw [l3_period_smul σ n h c v z, l3_period_smul σ n h c v (binaryComplexReflection z), map_smul]
  module

theorem lteCocycle_add (h : ℤ) (v v' : σ.H) (A : BinaryRealGL) :
    lteCocycle σ n h (v + v') A = lteCocycle σ n h v A + lteCocycle σ n h v' A := by
  unfold lteCocycle
  exact ltePotential_add σ n h v v' _ (basePoint_im_pos A)

theorem lteCocycle_smul (h : ℤ) (c : ℂ) (v : σ.H) (A : BinaryRealGL) :
    lteCocycle σ n h (c • v) A = c • lteCocycle σ n h v A := by
  unfold lteCocycle
  exact ltePotential_smul σ n h c v _

/-- **Additivity** of the scalar Eichler cocycle in the vector, when the Hilbert-level cocycle
values of the summands are smooth. -/
theorem lteAlpha_add (h : ℤ) (v v' : σ.H) (A : BinaryRealGL)
    (hv : ∀ position, lteCocycle σ n h v A position ∈ σ.smooth)
    (hv' : ∀ position, lteCocycle σ n h v' A position ∈ σ.smooth) :
    lteAlpha σ n h (v + v') A = lteAlpha σ n h v A + lteAlpha σ n h v' A := by
  unfold lteAlpha
  rw [lteCocycle_add σ n h v v' A, hilbertLift_add σ _ _ hv hv']

/-- **Homogeneity** of the scalar Eichler cocycle in the vector. -/
theorem lteAlpha_smul (h : ℤ) (c : ℂ) (v : σ.H) (A : BinaryRealGL)
    (hv : ∀ position, lteCocycle σ n h v A position ∈ σ.smooth) :
    lteAlpha σ n h (c • v) A = c • lteAlpha σ n h v A := by
  unfold lteAlpha
  rw [lteCocycle_smul σ n h c v A, hilbertLift_smul σ c _ hv]

end Linear

/-! ## The datum of a level-three weight vector -/

section Data

variable {σ : CuspidalRepresentation} {n : ℕ}

/-- The analytic stages of a cohomological cuspidal representation. -/
theorem levelThreeStages (coh : Cohomological σ n) : AnalyticScalar.ContinuousStages σ :=
  AnalyticClasses.continuousStages (⟨σ, trivialCharacter, coh⟩ : InducingData n)

/-- The Eichler input of a level-three classical vector of weight `-(n + 3)`. -/
def levelThreeEichlerInput (coh : Cohomological σ n) (hσ : LevelThreeCusp σ) (halfWeight : ℤ)
    (hw : 2 * halfWeight = -((n : ℤ) + 3)) (v : σ.smooth)
    (hv : v ∈ levelThreeClassicalVectors σ halfWeight) : L3Input σ n :=
  L3Input.ofWeightVector coh hσ halfWeight hw v hv.1 hv.2.1

/-- **The level-three Eichler Levi cocycle datum** of a level-three classical vector `v` of weight
`-(n + 3)`: its cocycle `α` is the Eichler integral of the holomorphic form of `v`
(see `levelThreeEichlerData_α`). -/
def levelThreeEichlerData (coh : Cohomological σ n) (hσ : LevelThreeCusp σ) (halfWeight : ℤ)
    (hw : 2 * halfWeight = -((n : ℤ) + 3)) (v : σ.smooth)
    (hv : v ∈ levelThreeClassicalVectors σ halfWeight) : LevelLeviCocycleData σ n :=
  lteData (levelThreeEichlerInput coh hσ halfWeight hw v hv) (levelThreeStages coh)

/-- **The cocycle of the datum is the Eichler integral of `v`**:
`α A = hilbertLift (½ (Per(A i) + J Per(-conj(A i))))`. -/
theorem levelThreeEichlerData_α (coh : Cohomological σ n) (hσ : LevelThreeCusp σ)
    (halfWeight : ℤ) (hw : 2 * halfWeight = -((n : ℤ) + 3)) (v : σ.smooth)
    (hv : v ∈ levelThreeClassicalVectors σ halfWeight) :
    (levelThreeEichlerData coh hσ halfWeight hw v hv).α = lteAlpha σ n halfWeight v.val := rfl

theorem levelThreeEichlerData_α_apply (coh : Cohomological σ n) (hσ : LevelThreeCusp σ)
    (halfWeight : ℤ) (hw : 2 * halfWeight = -((n : ℤ) + 3)) (v : σ.smooth)
    (hv : v ∈ levelThreeClassicalVectors σ halfWeight) (A : BinaryRealGL) :
    (levelThreeEichlerData coh hσ halfWeight hw v hv).α A =
      hilbertLift σ n ((2 : ℂ)⁻¹ • (binaryEndpointPeriod σ n halfWeight v.val (basePoint A) +
        binaryHilbertOperator σ (binaryWeightBasis (n + 1)) UpperHalfPlane.J
          (binaryEndpointPeriod σ n halfWeight v.val
            (binaryComplexReflection (basePoint A))))) := rfl

/-- The scalar Eichler cocycle of a level-three classical vector is additive and homogeneous in
the vector: it is a ℂ-linear map. -/
def lteFamilyMap (coh : Cohomological σ n) (hσ : LevelThreeCusp σ) (halfWeight : ℤ)
    (hw : 2 * halfWeight = -((n : ℤ) + 3)) :
    levelThreeClassicalVectors σ halfWeight →ₗ[ℂ]
      (BinaryRealGL → BinaryAdelicGL → Binary.HomogeneousPoly (n + 1)) where
  toFun w := lteAlpha σ n halfWeight w.val.val
  map_add' w w' := by
    funext A
    exact lteAlpha_add σ n halfWeight w.val.val w'.val.val A
      (fun position => lteCoc_smooth (levelThreeEichlerInput coh hσ halfWeight hw w.val w.property)
        (levelThreeStages coh) A position)
      (fun position => lteCoc_smooth
        (levelThreeEichlerInput coh hσ halfWeight hw w'.val w'.property)
        (levelThreeStages coh) A position)
  map_smul' c w := by
    funext A
    exact lteAlpha_smul σ n halfWeight c w.val.val A
      (fun position => lteCoc_smooth (levelThreeEichlerInput coh hσ halfWeight hw w.val w.property)
        (levelThreeStages coh) A position)

theorem levelThreeEichlerData_α_eq_family (coh : Cohomological σ n) (hσ : LevelThreeCusp σ)
    (halfWeight : ℤ) (hw : 2 * halfWeight = -((n : ℤ) + 3))
    (w : levelThreeClassicalVectors σ halfWeight) :
    (levelThreeEichlerData coh hσ halfWeight hw w.val w.property).α =
      lteFamilyMap coh hσ halfWeight hw w := rfl

theorem levelThreeEichlerData_α_add (coh : Cohomological σ n) (hσ : LevelThreeCusp σ)
    (halfWeight : ℤ) (hw : 2 * halfWeight = -((n : ℤ) + 3))
    (w w' : levelThreeClassicalVectors σ halfWeight) :
    (levelThreeEichlerData coh hσ halfWeight hw (w + w').val (w + w').property).α =
      (levelThreeEichlerData coh hσ halfWeight hw w.val w.property).α +
        (levelThreeEichlerData coh hσ halfWeight hw w'.val w'.property).α := by
  rw [levelThreeEichlerData_α_eq_family, levelThreeEichlerData_α_eq_family,
    levelThreeEichlerData_α_eq_family, map_add]

theorem levelThreeEichlerData_α_smul (coh : Cohomological σ n) (hσ : LevelThreeCusp σ)
    (halfWeight : ℤ) (hw : 2 * halfWeight = -((n : ℤ) + 3)) (c : ℂ)
    (w : levelThreeClassicalVectors σ halfWeight) :
    (levelThreeEichlerData coh hσ halfWeight hw (c • w).val (c • w).property).α =
      c • (levelThreeEichlerData coh hσ halfWeight hw w.val w.property).α := by
  rw [levelThreeEichlerData_α_eq_family, levelThreeEichlerData_α_eq_family, map_smul]

/-- A nonzero level-three vector gives a level-three cusp. -/
theorem levelThreeCusp_of_classical {halfWeight : ℤ} {v : σ.smooth}
    (hv : v ∈ levelThreeClassicalVectors σ halfWeight) (hne : v ≠ 0) : LevelThreeCusp σ :=
  ⟨v, hne, hv.1⟩

/-- **Existence of the level-three Eichler Levi cocycle datum** from a nonzero level-three
vector of weight `-(n + 3)` with holomorphic scalar realization. -/
theorem exists_levelLeviCocycleData (coh : Cohomological σ n) (halfWeight : ℤ)
    (hw : 2 * halfWeight = -((n : ℤ) + 3)) (v : σ.smooth)
    (hv : v ∈ levelThreeClassicalVectors σ halfWeight) (hne : v ≠ 0) :
    ∃ E : LevelLeviCocycleData σ n, E.α = lteAlpha σ n halfWeight v.val :=
  ⟨levelThreeEichlerData coh (levelThreeCusp_of_classical hv hne) halfWeight hw v hv,
    levelThreeEichlerData_α coh _ halfWeight hw v hv⟩

/-- **Existence of the level-three Eichler Levi cocycle datum** for a cohomological cuspidal
representation of odd degree with a nonzero level-three vector. -/
theorem exists_levelLeviCocycleData_of_levelThree (coh : Cohomological σ n) (hodd : Odd n)
    (level : ∃ v : σ.smooth, v ≠ 0 ∧ v.val ∈ levelThreeValues σ) :
    Nonempty (LevelLeviCocycleData σ n) := by
  obtain ⟨halfWeight, hw, v, hv, hne⟩ := cohomological_exists_levelThree_classical σ level hodd coh
  obtain ⟨E, _⟩ := exists_levelLeviCocycleData coh halfWeight hw v hv hne
  exact ⟨E⟩

end Data

end TernaryPeriodPolynomials.LevelThreeSource

end
