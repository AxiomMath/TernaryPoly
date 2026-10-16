module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Even.WtL3TwLinear
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Even.WtL3TwLiftB
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Even.WtHolomorphic
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.L3EichlerMain

@[expose] public section


/-!
# The weight-generic linear family of sign-twisted level-three Levi cocycles

Formalized by Claude Sonnet 5.5 (AxiomCode).

Twin of `AxiomCodeSourceConstruction/L3EichlerMain` (from `L3Input.ofWeightVector` on) for an
integer rotation weight `wt = -(n + 3)`, with no parity hypothesis on `n`: every vector `w` of
`levelThreeWeightVectors σ (-(n + 3))` is the input `L3InputWt.ofWeightVector` of the sign-twisted
Eichler construction, and the resulting cocycles `l3FamilyDataWt … w` depend linearly on `w`:
`(l3FamilyDataWt … w).α = l3FamilyMapWt … w` for a ℂ-linear map `l3FamilyMapWt`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.EvenLevelThree

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.PlaneEisensteinContinuation
open TernaryPeriodPolynomials.MultiplicityOne (LevelThreeCusp levelThreeValues)
open TernaryPeriodPolynomials.LevelThreeSource
  (levelThreeWeightVectors mem_levelThreeWeightVectors)
open TernaryPeriodPolynomials.SourceConstruction
  (LineLeviCocycleData3 levelThreeCusp_of_weightVector)

/-! ## The Eichler input of a level-three weight vector -/

/-- The Eichler input of a smooth level-three vector of weight `wt = -(n + 3)` in a cohomological
cuspidal representation with a level-three vector. -/
def L3InputWt.ofWeightVector {σ : CuspidalRepresentation} {n : ℕ} (coh : Cohomological σ n)
    (hσ : LevelThreeCusp σ) (wt : ℤ) (hw : wt = -((n : ℤ) + 3))
    (w : σ.smooth) (level : w.val ∈ levelThreeValues σ)
    (rotation : ∀ a : Circle, σ.π (atInfinity (binaryRotations a)) w.val =
      (a : ℂ) ^ wt • w.val) : L3InputWt σ n where
  central_positive := cohomological_centralCharacter_positive σ coh
  cusp3 := hσ
  wt := wt
  weight := hw
  vector := w
  vector_level := level
  rotation := rotation
  holomorphic := l3_holomorphicWt coh wt hw w rotation

/-! ## The linear family -/

section Family

variable {n : ℕ}

/-- The Eichler input of a level-three weight vector. -/
def l3FamilyInputWt (D : InducingData n) (hσ : LevelThreeCusp D.cusp) (wt : ℤ)
    (hw : wt = -((n : ℤ) + 3))
    (w : levelThreeWeightVectors D.cusp (-((n : ℤ) + 3))) : L3InputWt D.cusp n :=
  L3InputWt.ofWeightVector D.cohomological hσ wt hw w.val
    (mem_levelThreeWeightVectors.mp w.property).1
    (fun a => by
      rw [hw]
      exact (mem_levelThreeWeightVectors.mp w.property).2 a)

/-- The scalar twisted Eichler cocycle of a level-three weight vector. -/
def l3FamilyAlphaWt (D : InducingData n) (wt : ℤ)
    (w : levelThreeWeightVectors D.cusp (-((n : ℤ) + 3))) (A : BinaryRealGL) :
    BinaryAdelicGL → Binary.HomogeneousPoly (n + 1) :=
  l3AlphaWt D.cusp n wt w.val.val A

/-- **The linear map** `w ↦ (A ↦ α_w(A))` from the level-three weight vectors to the functions
on `GL₂(ℝ) × GL₂(𝔸)` with values in `Sym^{n+1}`. -/
def l3FamilyMapWt (D : InducingData n) (hσ : LevelThreeCusp D.cusp) (wt : ℤ)
    (hw : wt = -((n : ℤ) + 3))
    (stages : AnalyticScalar.ContinuousStages D.cusp) :
    levelThreeWeightVectors D.cusp (-((n : ℤ) + 3)) →ₗ[ℂ]
      (BinaryRealGL → BinaryAdelicGL → Binary.HomogeneousPoly (n + 1)) where
  toFun w := l3FamilyAlphaWt D wt w
  map_add' w w' := by
    funext A
    exact l3Alpha_addWt D.cusp n wt w.val.val w'.val.val A
      (fun position => (l3FamilyInputWt D hσ wt hw w).cocycle_smooth stages A position)
      (fun position => (l3FamilyInputWt D hσ wt hw w').cocycle_smooth stages A position)
  map_smul' c w := by
    funext A
    exact l3Alpha_smulWt D.cusp n wt c w.val.val A
      (fun position => (l3FamilyInputWt D hσ wt hw w).cocycle_smooth stages A position)

/-- **The sign-twisted level-three Levi cocycle datum of a weight vector.** -/
def l3FamilyDataWt (D : InducingData n) (hσ : LevelThreeCusp D.cusp) (wt : ℤ)
    (hw : wt = -((n : ℤ) + 3))
    (stages : AnalyticScalar.ContinuousStages D.cusp)
    (w : levelThreeWeightVectors D.cusp (-((n : ℤ) + 3))) : LineLeviCocycleData3 D.cusp n :=
  (l3FamilyInputWt D hσ wt hw w).toData stages

theorem l3FamilyData_αWt (D : InducingData n) (hσ : LevelThreeCusp D.cusp) (wt : ℤ)
    (hw : wt = -((n : ℤ) + 3))
    (stages : AnalyticScalar.ContinuousStages D.cusp)
    (w : levelThreeWeightVectors D.cusp (-((n : ℤ) + 3))) :
    (l3FamilyDataWt D hσ wt hw stages w).α = l3FamilyMapWt D hσ wt hw stages w := rfl

theorem l3FamilyData_α_addWt (D : InducingData n) (hσ : LevelThreeCusp D.cusp) (wt : ℤ)
    (hw : wt = -((n : ℤ) + 3))
    (stages : AnalyticScalar.ContinuousStages D.cusp)
    (w w' : levelThreeWeightVectors D.cusp (-((n : ℤ) + 3))) :
    (l3FamilyDataWt D hσ wt hw stages (w + w')).α =
      (l3FamilyDataWt D hσ wt hw stages w).α + (l3FamilyDataWt D hσ wt hw stages w').α := by
  rw [l3FamilyData_αWt, l3FamilyData_αWt, l3FamilyData_αWt, map_add]

theorem l3FamilyData_α_smulWt (D : InducingData n) (hσ : LevelThreeCusp D.cusp) (wt : ℤ)
    (hw : wt = -((n : ℤ) + 3))
    (stages : AnalyticScalar.ContinuousStages D.cusp) (c : ℂ)
    (w : levelThreeWeightVectors D.cusp (-((n : ℤ) + 3))) :
    (l3FamilyDataWt D hσ wt hw stages (c • w)).α =
      c • (l3FamilyDataWt D hσ wt hw stages w).α := by
  rw [l3FamilyData_αWt, l3FamilyData_αWt, map_smul]

end Family

/-- **The linear family of sign-twisted level-three Levi cocycles, for every degree.**  For an
inducing datum whose cuspidal representation has a nonzero level-three vector, every level-three
vector of weight `-(n + 3)` has a sign-twisted Levi cocycle datum `E w` (with lifts fixed only by
the bad-line Levi level), and `w ↦ (E w).α` is additive and homogeneous. -/
theorem exists_levelThreeEichlerFamilyWt {n : ℕ} (D : InducingData n)
    (hσ : LevelThreeCusp D.cusp) :
    ∃ E : levelThreeWeightVectors D.cusp (-((n : ℤ) + 3)) → LineLeviCocycleData3 D.cusp n,
      (∀ w w', (E (w + w')).α = (E w).α + (E w').α) ∧
      (∀ (c : ℂ) w, (E (c • w)).α = c • (E w).α) :=
  ⟨l3FamilyDataWt D hσ (-((n : ℤ) + 3)) rfl (AnalyticClasses.continuousStages D),
    fun w w' => l3FamilyData_α_addWt D hσ (-((n : ℤ) + 3)) rfl
      (AnalyticClasses.continuousStages D) w w',
    fun c w => l3FamilyData_α_smulWt D hσ (-((n : ℤ) + 3)) rfl
      (AnalyticClasses.continuousStages D) c w⟩

/-- **The linear-map form**: the sign-twisted level-three Levi cocycle data `E w` of the level-three
weight vectors of weight `-(n + 3)` have `α` given by a ℂ-linear map `T`. -/
theorem exists_levelThreeEichlerLinearWt {n : ℕ} (D : InducingData n)
    (hσ : LevelThreeCusp D.cusp) :
    ∃ (E : levelThreeWeightVectors D.cusp (-((n : ℤ) + 3)) → LineLeviCocycleData3 D.cusp n)
      (T : levelThreeWeightVectors D.cusp (-((n : ℤ) + 3)) →ₗ[ℂ]
        (BinaryRealGL → BinaryAdelicGL → Binary.HomogeneousPoly (n + 1))),
      ∀ w, (E w).α = T w :=
  ⟨l3FamilyDataWt D hσ (-((n : ℤ) + 3)) rfl (AnalyticClasses.continuousStages D),
    l3FamilyMapWt D hσ (-((n : ℤ) + 3)) rfl (AnalyticClasses.continuousStages D),
    fun w => l3FamilyData_αWt D hσ (-((n : ℤ) + 3)) rfl (AnalyticClasses.continuousStages D) w⟩

/-- The same, with the additivity and homogeneity stated pointwise. -/
theorem exists_levelThreeEichlerFamily_applyWt {n : ℕ} (D : InducingData n)
    (hσ : LevelThreeCusp D.cusp) :
    ∃ E : levelThreeWeightVectors D.cusp (-((n : ℤ) + 3)) → LineLeviCocycleData3 D.cusp n,
      (∀ w w' g x, (E (w + w')).α g x = (E w).α g x + (E w').α g x) ∧
      (∀ (c : ℂ) w g x, (E (c • w)).α g x = c • (E w).α g x) := by
  obtain ⟨E, hadd, hsmul⟩ := exists_levelThreeEichlerFamilyWt D hσ
  exact ⟨E, fun w w' g x => congrFun (congrFun (hadd w w') g) x,
    fun c w g x => congrFun (congrFun (hsmul c w) g) x⟩

/-- The same, from a nonzero level-three weight vector. -/
theorem exists_levelThreeEichlerFamily_of_neWt {n : ℕ} (D : InducingData n)
    (w₀ : levelThreeWeightVectors D.cusp (-((n : ℤ) + 3))) (hw₀ : w₀ ≠ 0) :
    ∃ E : levelThreeWeightVectors D.cusp (-((n : ℤ) + 3)) → LineLeviCocycleData3 D.cusp n,
      (∀ w w' g x, (E (w + w')).α g x = (E w).α g x + (E w').α g x) ∧
      (∀ (c : ℂ) w g x, (E (c • w)).α g x = c • (E w).α g x) :=
  exists_levelThreeEichlerFamily_applyWt D (levelThreeCusp_of_weightVector w₀ hw₀)

end TernaryPeriodPolynomials.EvenLevelThree

end
