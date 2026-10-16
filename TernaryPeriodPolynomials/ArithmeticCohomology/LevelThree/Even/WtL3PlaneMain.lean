module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Even.WtL3PlaneB
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Even.WtL3TwMain
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Source.LevelThreeEichlerMain
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Source.Vectors

@[expose] public section


/-!
# The weight-generic level-three Eichler Levi cocycle datum

Formalized by Claude Sonnet 5.5 (AxiomCode).

Twin of `AxiomCodeLevelThreeSource/LevelThreeEichlerMain` for an integer rotation weight
`wt = -(n + 3)`, with no parity hypothesis on `n`.

* `levelThreeEichlerDataWt coh hσ wt hw v hv : LevelLeviCocycleData σ n` is the datum built from a
  level-three weight vector `v` (a member of `levelThreeWeightVectors σ wt`) in a cohomological
  cuspidal representation `σ`; its cocycle is the Eichler integral of the holomorphic form of `v`
  (`levelThreeEichlerData_αWt` : `α = lteAlphaWt σ n wt v`).
* `lteAlphaWt` is additive and homogeneous in the vector (`lteAlpha_addWt`, `lteAlpha_smulWt`), so
  the cocycles of the level-three weight vectors form a linear family (`lteFamilyMapWt`,
  `l3PlaneFamilyMapWt`).
* `exists_levelLeviCocycleDataWt` : existence of the datum from a nonzero level-three weight
  vector; `exists_levelThreeEichlerLinearPlaneWt` : the linear-family form for an inducing datum.
-/

noncomputable section

namespace TernaryPeriodPolynomials.EvenLevelThree

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.AnalyticClasses
open TernaryPeriodPolynomials.PlaneEisensteinContinuation
open TernaryPeriodPolynomials.MultiplicityOne (LevelThreeCusp)
open TernaryPeriodPolynomials.LevelThreeSource
  (LevelLeviCocycleData levelThreeWeightVectors mem_levelThreeWeightVectors levelThreeStages)

/-! ## Linearity in the vector -/

section Linear

variable (σ : CuspidalRepresentation) (n : ℕ)

theorem ltePotential_addWt (wt : ℤ) (v v' : σ.H) (z : ℂ) (hz : 0 < z.im) :
    l3PlanePotentialWt σ n wt (v + v') z =
      l3PlanePotentialWt σ n wt v z + l3PlanePotentialWt σ n wt v' z := by
  have hz' : 0 < (binaryComplexReflection z).im := by
    rw [binaryComplexReflection_im]
    exact hz
  unfold l3PlanePotentialWt
  rw [l3_period_addWt σ n wt v v' z hz, l3_period_addWt σ n wt v v' (binaryComplexReflection z) hz',
    map_add]
  module

theorem ltePotential_smulWt (wt : ℤ) (c : ℂ) (v : σ.H) (z : ℂ) :
    l3PlanePotentialWt σ n wt (c • v) z = c • l3PlanePotentialWt σ n wt v z := by
  unfold l3PlanePotentialWt
  rw [l3_period_smulWt σ n wt c v z, l3_period_smulWt σ n wt c v (binaryComplexReflection z),
    map_smul]
  module

theorem lteCocycle_addWt (wt : ℤ) (v v' : σ.H) (A : BinaryRealGL) :
    l3PlaneCocycleWt σ n wt (v + v') A =
      l3PlaneCocycleWt σ n wt v A + l3PlaneCocycleWt σ n wt v' A := by
  unfold l3PlaneCocycleWt
  exact ltePotential_addWt σ n wt v v' _ (basePoint_im_pos A)

theorem lteCocycle_smulWt (wt : ℤ) (c : ℂ) (v : σ.H) (A : BinaryRealGL) :
    l3PlaneCocycleWt σ n wt (c • v) A = c • l3PlaneCocycleWt σ n wt v A := by
  unfold l3PlaneCocycleWt
  exact ltePotential_smulWt σ n wt c v _

/-- **Additivity** of the scalar Eichler cocycle in the vector, when the Hilbert-level cocycle
values of the summands are smooth. -/
theorem lteAlpha_addWt (wt : ℤ) (v v' : σ.H) (A : BinaryRealGL)
    (hv : ∀ position, l3PlaneCocycleWt σ n wt v A position ∈ σ.smooth)
    (hv' : ∀ position, l3PlaneCocycleWt σ n wt v' A position ∈ σ.smooth) :
    lteAlphaWt σ n wt (v + v') A = lteAlphaWt σ n wt v A + lteAlphaWt σ n wt v' A := by
  unfold lteAlphaWt
  rw [lteCocycle_addWt σ n wt v v' A, hilbertLift_add σ _ _ hv hv']

/-- **Homogeneity** of the scalar Eichler cocycle in the vector. -/
theorem lteAlpha_smulWt (wt : ℤ) (c : ℂ) (v : σ.H) (A : BinaryRealGL)
    (hv : ∀ position, l3PlaneCocycleWt σ n wt v A position ∈ σ.smooth) :
    lteAlphaWt σ n wt (c • v) A = c • lteAlphaWt σ n wt v A := by
  unfold lteAlphaWt
  rw [lteCocycle_smulWt σ n wt c v A, hilbertLift_smul σ c _ hv]

end Linear

/-! ## The datum of a level-three weight vector -/

section Data

variable {σ : CuspidalRepresentation} {n : ℕ}

/-- The Eichler input of a level-three weight vector of weight `wt = -(n + 3)`. -/
def levelThreeEichlerInputWt (coh : Cohomological σ n) (hσ : LevelThreeCusp σ) (wt : ℤ)
    (hw : wt = -((n : ℤ) + 3)) (v : σ.smooth) (hv : v ∈ levelThreeWeightVectors σ wt) :
    L3InputWt σ n :=
  L3InputWt.ofWeightVector coh hσ wt hw v (mem_levelThreeWeightVectors.mp hv).1
    (mem_levelThreeWeightVectors.mp hv).2

/-- **The level-three Eichler Levi cocycle datum** of a level-three weight vector `v` of weight
`wt = -(n + 3)`: its cocycle `α` is the Eichler integral of the holomorphic form of `v`
(see `levelThreeEichlerData_αWt`). -/
def levelThreeEichlerDataWt (coh : Cohomological σ n) (hσ : LevelThreeCusp σ) (wt : ℤ)
    (hw : wt = -((n : ℤ) + 3)) (v : σ.smooth) (hv : v ∈ levelThreeWeightVectors σ wt) :
    LevelLeviCocycleData σ n :=
  lteDataWt (levelThreeEichlerInputWt coh hσ wt hw v hv) (levelThreeStages coh)

/-- **The cocycle of the datum is the Eichler integral of `v`**. -/
theorem levelThreeEichlerData_αWt (coh : Cohomological σ n) (hσ : LevelThreeCusp σ) (wt : ℤ)
    (hw : wt = -((n : ℤ) + 3)) (v : σ.smooth) (hv : v ∈ levelThreeWeightVectors σ wt) :
    (levelThreeEichlerDataWt coh hσ wt hw v hv).α = lteAlphaWt σ n wt v.val := rfl

theorem levelThreeEichlerData_α_applyWt (coh : Cohomological σ n) (hσ : LevelThreeCusp σ)
    (wt : ℤ) (hw : wt = -((n : ℤ) + 3)) (v : σ.smooth) (hv : v ∈ levelThreeWeightVectors σ wt)
    (A : BinaryRealGL) :
    (levelThreeEichlerDataWt coh hσ wt hw v hv).α A =
      hilbertLift σ n ((2 : ℂ)⁻¹ • (binaryEndpointPeriodWt σ n wt v.val (basePoint A) +
        binaryHilbertOperator σ (binaryWeightBasis (n + 1)) UpperHalfPlane.J
          (binaryEndpointPeriodWt σ n wt v.val (binaryComplexReflection (basePoint A))))) := rfl

/-- The scalar Eichler cocycle of a level-three weight vector is additive and homogeneous in the
vector: it is a ℂ-linear map. -/
def lteFamilyMapWt (coh : Cohomological σ n) (hσ : LevelThreeCusp σ) (wt : ℤ)
    (hw : wt = -((n : ℤ) + 3)) :
    levelThreeWeightVectors σ wt →ₗ[ℂ]
      (BinaryRealGL → BinaryAdelicGL → Binary.HomogeneousPoly (n + 1)) where
  toFun w := lteAlphaWt σ n wt w.val.val
  map_add' w w' := by
    funext A
    exact lteAlpha_addWt σ n wt w.val.val w'.val.val A
      (fun position => lteCocWt_smooth (levelThreeEichlerInputWt coh hσ wt hw w.val w.property)
        (levelThreeStages coh) A position)
      (fun position => lteCocWt_smooth (levelThreeEichlerInputWt coh hσ wt hw w'.val w'.property)
        (levelThreeStages coh) A position)
  map_smul' c w := by
    funext A
    exact lteAlpha_smulWt σ n wt c w.val.val A
      (fun position => lteCocWt_smooth (levelThreeEichlerInputWt coh hσ wt hw w.val w.property)
        (levelThreeStages coh) A position)

theorem levelThreeEichlerData_α_eq_familyWt (coh : Cohomological σ n) (hσ : LevelThreeCusp σ)
    (wt : ℤ) (hw : wt = -((n : ℤ) + 3)) (w : levelThreeWeightVectors σ wt) :
    (levelThreeEichlerDataWt coh hσ wt hw w.val w.property).α = lteFamilyMapWt coh hσ wt hw w :=
  rfl

theorem levelThreeEichlerData_α_addWt (coh : Cohomological σ n) (hσ : LevelThreeCusp σ)
    (wt : ℤ) (hw : wt = -((n : ℤ) + 3)) (w w' : levelThreeWeightVectors σ wt) :
    (levelThreeEichlerDataWt coh hσ wt hw (w + w').val (w + w').property).α =
      (levelThreeEichlerDataWt coh hσ wt hw w.val w.property).α +
        (levelThreeEichlerDataWt coh hσ wt hw w'.val w'.property).α := by
  rw [levelThreeEichlerData_α_eq_familyWt, levelThreeEichlerData_α_eq_familyWt,
    levelThreeEichlerData_α_eq_familyWt, map_add]

theorem levelThreeEichlerData_α_smulWt (coh : Cohomological σ n) (hσ : LevelThreeCusp σ)
    (wt : ℤ) (hw : wt = -((n : ℤ) + 3)) (c : ℂ) (w : levelThreeWeightVectors σ wt) :
    (levelThreeEichlerDataWt coh hσ wt hw (c • w).val (c • w).property).α =
      c • (levelThreeEichlerDataWt coh hσ wt hw w.val w.property).α := by
  rw [levelThreeEichlerData_α_eq_familyWt, levelThreeEichlerData_α_eq_familyWt, map_smul]

/-- **Existence of the level-three Eichler Levi cocycle datum** from a nonzero level-three vector
of rotation weight `wt = -(n + 3)`, for every parity of `n`. -/
theorem exists_levelLeviCocycleDataWt (coh : Cohomological σ n) (wt : ℤ)
    (hw : wt = -((n : ℤ) + 3)) (v : σ.smooth) (hv : v ∈ levelThreeWeightVectors σ wt)
    (hne : v ≠ 0) :
    ∃ E : LevelLeviCocycleData σ n, E.α = lteAlphaWt σ n wt v.val :=
  ⟨levelThreeEichlerDataWt coh ⟨v, hne, (mem_levelThreeWeightVectors.mp hv).1⟩ wt hw v hv,
    levelThreeEichlerData_αWt coh _ wt hw v hv⟩

/-- **Existence of the level-three Eichler Levi cocycle datum** for a cohomological cuspidal
representation with a nonzero level-three vector of weight `-(n + 3)`. -/
theorem exists_levelLeviCocycleData_of_weightVectorWt (coh : Cohomological σ n)
    (level : ∃ v : σ.smooth, v ≠ 0 ∧ v ∈ levelThreeWeightVectors σ (-((n : ℤ) + 3))) :
    Nonempty (LevelLeviCocycleData σ n) := by
  obtain ⟨v, hne, hv⟩ := level
  obtain ⟨E, _⟩ := exists_levelLeviCocycleDataWt coh (-((n : ℤ) + 3)) rfl v hv hne
  exact ⟨E⟩

end Data

/-! ## The linear family over an inducing datum -/

section Family

variable {n : ℕ}

/-- The Eichler input of a level-three weight vector (the input `l3FamilyInputWt` of the
weight-generic family). -/
abbrev l3PlaneFamilyInputWt (D : InducingData n) (hσ : LevelThreeCusp D.cusp) (wt : ℤ)
    (hw : wt = -((n : ℤ) + 3))
    (w : levelThreeWeightVectors D.cusp (-((n : ℤ) + 3))) : L3InputWt D.cusp n :=
  l3FamilyInputWt D hσ wt hw w

/-- **The level-three Levi cocycle datum of a weight vector.** -/
def l3PlaneFamilyDataWt (D : InducingData n) (hσ : LevelThreeCusp D.cusp) (wt : ℤ)
    (hw : wt = -((n : ℤ) + 3)) (stages : AnalyticScalar.ContinuousStages D.cusp)
    (w : levelThreeWeightVectors D.cusp (-((n : ℤ) + 3))) : LevelLeviCocycleData D.cusp n :=
  lteDataWt (l3PlaneFamilyInputWt D hσ wt hw w) stages

/-- **The linear map** `w ↦ (A ↦ α_w(A))` from the level-three weight vectors to the functions on
`GL₂(ℝ) × GL₂(𝔸)` with values in `Sym^{n+1}`. -/
def l3PlaneFamilyMapWt (D : InducingData n) (hσ : LevelThreeCusp D.cusp) (wt : ℤ)
    (hw : wt = -((n : ℤ) + 3)) (stages : AnalyticScalar.ContinuousStages D.cusp) :
    levelThreeWeightVectors D.cusp (-((n : ℤ) + 3)) →ₗ[ℂ]
      (BinaryRealGL → BinaryAdelicGL → Binary.HomogeneousPoly (n + 1)) where
  toFun w := lteAlphaWt D.cusp n wt w.val.val
  map_add' w w' := by
    funext A
    exact lteAlpha_addWt D.cusp n wt w.val.val w'.val.val A
      (fun position => lteCocWt_smooth (l3PlaneFamilyInputWt D hσ wt hw w) stages A position)
      (fun position => lteCocWt_smooth (l3PlaneFamilyInputWt D hσ wt hw w') stages A position)
  map_smul' c w := by
    funext A
    exact lteAlpha_smulWt D.cusp n wt c w.val.val A
      (fun position => lteCocWt_smooth (l3PlaneFamilyInputWt D hσ wt hw w) stages A position)

theorem l3PlaneFamilyData_αWt (D : InducingData n) (hσ : LevelThreeCusp D.cusp) (wt : ℤ)
    (hw : wt = -((n : ℤ) + 3)) (stages : AnalyticScalar.ContinuousStages D.cusp)
    (w : levelThreeWeightVectors D.cusp (-((n : ℤ) + 3))) :
    (l3PlaneFamilyDataWt D hσ wt hw stages w).α = lteAlphaWt D.cusp n wt w.val.val := rfl

theorem l3PlaneFamilyData_α_mapWt (D : InducingData n) (hσ : LevelThreeCusp D.cusp) (wt : ℤ)
    (hw : wt = -((n : ℤ) + 3)) (stages : AnalyticScalar.ContinuousStages D.cusp)
    (w : levelThreeWeightVectors D.cusp (-((n : ℤ) + 3))) :
    (l3PlaneFamilyDataWt D hσ wt hw stages w).α = l3PlaneFamilyMapWt D hσ wt hw stages w := rfl

theorem l3PlaneFamilyData_α_addWt (D : InducingData n) (hσ : LevelThreeCusp D.cusp) (wt : ℤ)
    (hw : wt = -((n : ℤ) + 3)) (stages : AnalyticScalar.ContinuousStages D.cusp)
    (w w' : levelThreeWeightVectors D.cusp (-((n : ℤ) + 3))) :
    (l3PlaneFamilyDataWt D hσ wt hw stages (w + w')).α =
      (l3PlaneFamilyDataWt D hσ wt hw stages w).α +
        (l3PlaneFamilyDataWt D hσ wt hw stages w').α := by
  rw [l3PlaneFamilyData_α_mapWt, l3PlaneFamilyData_α_mapWt, l3PlaneFamilyData_α_mapWt, map_add]

theorem l3PlaneFamilyData_α_smulWt (D : InducingData n) (hσ : LevelThreeCusp D.cusp) (wt : ℤ)
    (hw : wt = -((n : ℤ) + 3)) (stages : AnalyticScalar.ContinuousStages D.cusp) (c : ℂ)
    (w : levelThreeWeightVectors D.cusp (-((n : ℤ) + 3))) :
    (l3PlaneFamilyDataWt D hσ wt hw stages (c • w)).α =
      c • (l3PlaneFamilyDataWt D hσ wt hw stages w).α := by
  rw [l3PlaneFamilyData_α_mapWt, l3PlaneFamilyData_α_mapWt, map_smul]

end Family

/-- **The linear family of level-three Levi cocycles, for every degree.**  For an inducing datum
whose cuspidal representation has a nonzero level-three vector, every level-three vector of weight
`-(n + 3)` has a level-three Levi cocycle datum `E w`, and `w ↦ (E w).α` is additive and
homogeneous. -/
theorem exists_levelThreeEichlerFamilyPlaneWt {n : ℕ} (D : InducingData n)
    (hσ : LevelThreeCusp D.cusp) :
    ∃ E : levelThreeWeightVectors D.cusp (-((n : ℤ) + 3)) → LevelLeviCocycleData D.cusp n,
      (∀ w w', (E (w + w')).α = (E w).α + (E w').α) ∧
      (∀ (c : ℂ) w, (E (c • w)).α = c • (E w).α) :=
  ⟨l3PlaneFamilyDataWt D hσ (-((n : ℤ) + 3)) rfl (AnalyticClasses.continuousStages D),
    fun w w' => l3PlaneFamilyData_α_addWt D hσ (-((n : ℤ) + 3)) rfl
      (AnalyticClasses.continuousStages D) w w',
    fun c w => l3PlaneFamilyData_α_smulWt D hσ (-((n : ℤ) + 3)) rfl
      (AnalyticClasses.continuousStages D) c w⟩

/-- **The linear-map form**: the level-three Levi cocycle data `E w` of the level-three weight
vectors of weight `-(n + 3)` have `α` given by a ℂ-linear map `T`. -/
theorem exists_levelThreeEichlerLinearPlaneWt {n : ℕ} (D : InducingData n)
    (hσ : LevelThreeCusp D.cusp) :
    ∃ (E : levelThreeWeightVectors D.cusp (-((n : ℤ) + 3)) → LevelLeviCocycleData D.cusp n)
      (T : levelThreeWeightVectors D.cusp (-((n : ℤ) + 3)) →ₗ[ℂ]
        (BinaryRealGL → BinaryAdelicGL → Binary.HomogeneousPoly (n + 1))),
      ∀ w, (E w).α = T w :=
  ⟨l3PlaneFamilyDataWt D hσ (-((n : ℤ) + 3)) rfl (AnalyticClasses.continuousStages D),
    l3PlaneFamilyMapWt D hσ (-((n : ℤ) + 3)) rfl (AnalyticClasses.continuousStages D),
    fun w => l3PlaneFamilyData_α_mapWt D hσ (-((n : ℤ) + 3)) rfl
      (AnalyticClasses.continuousStages D) w⟩

end TernaryPeriodPolynomials.EvenLevelThree

end
