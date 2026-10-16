module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.L3EichlerLinear
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.AnalyticWeight
public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Good.LineUniformDecay
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.LadderClosures
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.HolomorphicOrbit
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Cohomological.HilbertRotationGap
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Cusp.RotationProjections

@[expose] public section


/-!
# The level-three sign-twisted Eichler cocycle, linear in the weight vector

For a cohomological cuspidal representation `σ` of odd degree `n` every smooth vector of rotation
weight `-(n + 3)` is holomorphic: its raising image has rotation weight `-(n + 1)`, which is excluded
by the Casimir weight gap `cohomological_hilbert_projection_zero`, so the raising image vanishes
(`l3_raising_eq_zero`) and the weighted affine orbit is holomorphic (`l3_holomorphic`).  Hence each
vector `w` of `levelThreeWeightVectors σ (-(n + 3))` is the input of the sign-twisted Eichler
construction (`L3Input.ofWeightVector`), and the resulting cocycles `l3FamilyData … w` depend
linearly on `w`: `(l3FamilyData … w).α = l3FamilyMap … w` for a ℂ-linear map `l3FamilyMap`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.SourceConstruction

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.PlaneEisensteinContinuation
open TernaryPeriodPolynomials.EisensteinRegularization.Helpers
  (binaryCircleRotation cuspCircularOrbit cuspRotationProjection_of_character
    cohomological_hilbert_projection_zero)
open TernaryPeriodPolynomials.MultiplicityOne (LevelThreeCusp levelThreeValues)
open TernaryPeriodPolynomials.LevelThreeSource
  (levelThreeWeightVectors mem_levelThreeWeightVectors)

/-! ## Every weight `-(n + 3)` vector is holomorphic -/

section Holomorphic

/-- A vector on which the rotations act through `a ↦ a ^ m` is an eigenvector of the circular
orbit with the character of weight `-m`. -/
theorem l3_circularOrbit_eq (σ : CuspidalRepresentation) (u : σ.H) (m : ℤ)
    (hrot : ∀ a : Circle, σ.π (atInfinity (binaryRotations a)) u = (a : ℂ) ^ m • u)
    (angle : AddCircle (1 : ℝ)) :
    cuspCircularOrbit σ u angle = fourier (-m) angle • u := by
  unfold cuspCircularOrbit
  have h1 : binaryCircleRotation angle.toCircle = binaryRotations (angle.toCircle)⁻¹ := by
    have := binaryRotations_eq_circleRotation_inv (angle.toCircle)⁻¹
    rw [inv_inv] at this
    exact this.symm
  rw [h1, hrot, circle_coe_inv, _root_.inv_zpow, fourier_apply, AddCircle.toCircle_zsmul,
    Circle.coe_zpow, _root_.zpow_neg]

/-- **The raising image of a weight `-(n + 3)` smooth vector vanishes.** -/
theorem l3_raising_eq_zero {σ : CuspidalRepresentation} {n : ℕ} (coh : Cohomological σ n)
    (halfWeight : ℤ) (hw : 2 * halfWeight = -((n : ℤ) + 3)) (w : σ.smooth)
    (rotation : ∀ a : Circle, σ.π (atInfinity (binaryRotations a)) w.val =
      (a : ℂ) ^ (2 * halfWeight) • w.val) :
    cuspRaisingVector σ (2 * halfWeight) w.val = 0 := by
  have regular : ContDiffOn ℝ (↑(⊤ : ℕ∞)) (cuspAffineOrbitVector σ w.val)
      UpperHalfPlane.upperHalfPlaneSet := cuspSmooth_le_affineSmooth σ w.property
  have rotated := cuspRaisingVector_rotation σ w.val (2 * halfWeight) regular rotation
  have character := l3_circularOrbit_eq σ (cuspRaisingVector σ (2 * halfWeight) w.val)
    (2 * halfWeight + 2) rotated
  have value : (((-(2 * halfWeight + 2) : ℤ)) : ℝ) = (n : ℝ) + 1 := by
    have e : (-(2 * halfWeight + 2) : ℤ) = (n : ℤ) + 1 := by omega
    exact_mod_cast e
  have forbidden : |(((-(2 * halfWeight + 2) : ℤ)) : ℝ)| < (n : ℝ) + 3 := by
    have nonneg : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
    rw [value, abs_of_nonneg nonneg]
    linarith
  have projection_zero := cohomological_hilbert_projection_zero coh (-(2 * halfWeight + 2))
    forbidden (cuspRaisingVector σ (2 * halfWeight) w.val)
  have projected := cuspRotationProjection_of_character σ (-(2 * halfWeight + 2))
    (-(2 * halfWeight + 2)) _ character
  rw [ite_eq_left rfl, projection_zero] at projected
  exact projected.symm

/-- **Every smooth vector of weight `-(n + 3)` is holomorphic** (no level hypothesis). -/
theorem l3_holomorphic {σ : CuspidalRepresentation} {n : ℕ} (coh : Cohomological σ n)
    (halfWeight : ℤ) (hw : 2 * halfWeight = -((n : ℤ) + 3)) (w : σ.smooth)
    (rotation : ∀ a : Circle, σ.π (atInfinity (binaryRotations a)) w.val =
      (a : ℂ) ^ (2 * halfWeight) • w.val) :
    DifferentiableOn ℂ (cuspWeightedAffineOrbit σ halfWeight w.val)
      UpperHalfPlane.upperHalfPlaneSet := by
  have regular : ContDiffOn ℝ (↑(⊤ : ℕ∞)) (cuspAffineOrbitVector σ w.val)
      UpperHalfPlane.upperHalfPlaneSet := cuspSmooth_le_affineSmooth σ w.property
  exact cuspWeightedAffineOrbit_holomorphic σ halfWeight w.val (regular.differentiableOn (by simp))
    (l3_raising_eq_zero coh halfWeight hw w rotation)

end Holomorphic

/-! ## The Eichler input of a level-three weight vector -/

/-- The Eichler input of a smooth level-three vector of weight `-(n + 3)` in a cohomological
cuspidal representation with a level-three vector. -/
def L3Input.ofWeightVector {σ : CuspidalRepresentation} {n : ℕ} (coh : Cohomological σ n)
    (hσ : LevelThreeCusp σ) (halfWeight : ℤ) (hw : 2 * halfWeight = -((n : ℤ) + 3))
    (w : σ.smooth) (level : w.val ∈ levelThreeValues σ)
    (rotation : ∀ a : Circle, σ.π (atInfinity (binaryRotations a)) w.val =
      (a : ℂ) ^ (2 * halfWeight) • w.val) : L3Input σ n where
  central_positive := cohomological_centralCharacter_positive σ coh
  cusp3 := hσ
  halfWeight := halfWeight
  weight := hw
  vector := w
  vector_level := level
  rotation := rotation
  holomorphic := l3_holomorphic coh halfWeight hw w rotation

/-! ## The linear family -/

section Family

variable {n : ℕ}

/-- The Eichler input of a level-three weight vector. -/
def l3FamilyInput (D : InducingData n) (hσ : LevelThreeCusp D.cusp) (halfWeight : ℤ)
    (hw : 2 * halfWeight = -((n : ℤ) + 3))
    (w : levelThreeWeightVectors D.cusp (-((n : ℤ) + 3))) : L3Input D.cusp n :=
  L3Input.ofWeightVector D.cohomological hσ halfWeight hw w.val
    (mem_levelThreeWeightVectors.mp w.property).1
    (fun a => by
      rw [hw]
      exact (mem_levelThreeWeightVectors.mp w.property).2 a)

/-- The scalar twisted Eichler cocycle of a level-three weight vector. -/
def l3FamilyAlpha (D : InducingData n) (halfWeight : ℤ)
    (w : levelThreeWeightVectors D.cusp (-((n : ℤ) + 3))) (A : BinaryRealGL) :
    BinaryAdelicGL → Binary.HomogeneousPoly (n + 1) :=
  l3Alpha D.cusp n halfWeight w.val.val A

/-- **The linear map** `w ↦ (A ↦ α_w(A))` from the level-three weight vectors to the functions
on `GL₂(ℝ) × GL₂(𝔸)` with values in `Sym^{n+1}`. -/
def l3FamilyMap (D : InducingData n) (hσ : LevelThreeCusp D.cusp) (halfWeight : ℤ)
    (hw : 2 * halfWeight = -((n : ℤ) + 3))
    (stages : AnalyticScalar.ContinuousStages D.cusp) :
    levelThreeWeightVectors D.cusp (-((n : ℤ) + 3)) →ₗ[ℂ]
      (BinaryRealGL → BinaryAdelicGL → Binary.HomogeneousPoly (n + 1)) where
  toFun w := l3FamilyAlpha D halfWeight w
  map_add' w w' := by
    funext A
    exact l3Alpha_add D.cusp n halfWeight w.val.val w'.val.val A
      (fun position => (l3FamilyInput D hσ halfWeight hw w).cocycle_smooth stages A position)
      (fun position => (l3FamilyInput D hσ halfWeight hw w').cocycle_smooth stages A position)
  map_smul' c w := by
    funext A
    exact l3Alpha_smul D.cusp n halfWeight c w.val.val A
      (fun position => (l3FamilyInput D hσ halfWeight hw w).cocycle_smooth stages A position)

/-- **The sign-twisted level-three Levi cocycle datum of a weight vector.** -/
def l3FamilyData (D : InducingData n) (hσ : LevelThreeCusp D.cusp) (halfWeight : ℤ)
    (hw : 2 * halfWeight = -((n : ℤ) + 3))
    (stages : AnalyticScalar.ContinuousStages D.cusp)
    (w : levelThreeWeightVectors D.cusp (-((n : ℤ) + 3))) : LineLeviCocycleData3 D.cusp n :=
  (l3FamilyInput D hσ halfWeight hw w).toData stages

theorem l3FamilyData_α (D : InducingData n) (hσ : LevelThreeCusp D.cusp) (halfWeight : ℤ)
    (hw : 2 * halfWeight = -((n : ℤ) + 3))
    (stages : AnalyticScalar.ContinuousStages D.cusp)
    (w : levelThreeWeightVectors D.cusp (-((n : ℤ) + 3))) :
    (l3FamilyData D hσ halfWeight hw stages w).α = l3FamilyMap D hσ halfWeight hw stages w := rfl

theorem l3FamilyData_α_add (D : InducingData n) (hσ : LevelThreeCusp D.cusp) (halfWeight : ℤ)
    (hw : 2 * halfWeight = -((n : ℤ) + 3))
    (stages : AnalyticScalar.ContinuousStages D.cusp)
    (w w' : levelThreeWeightVectors D.cusp (-((n : ℤ) + 3))) :
    (l3FamilyData D hσ halfWeight hw stages (w + w')).α =
      (l3FamilyData D hσ halfWeight hw stages w).α +
        (l3FamilyData D hσ halfWeight hw stages w').α := by
  rw [l3FamilyData_α, l3FamilyData_α, l3FamilyData_α, map_add]

theorem l3FamilyData_α_smul (D : InducingData n) (hσ : LevelThreeCusp D.cusp) (halfWeight : ℤ)
    (hw : 2 * halfWeight = -((n : ℤ) + 3))
    (stages : AnalyticScalar.ContinuousStages D.cusp) (c : ℂ)
    (w : levelThreeWeightVectors D.cusp (-((n : ℤ) + 3))) :
    (l3FamilyData D hσ halfWeight hw stages (c • w)).α =
      c • (l3FamilyData D hσ halfWeight hw stages w).α := by
  rw [l3FamilyData_α, l3FamilyData_α, map_smul]

end Family

/-- A nonzero level-three weight vector gives a level-three cusp. -/
theorem levelThreeCusp_of_weightVector {σ : CuspidalRepresentation} {weight : ℤ}
    (w : levelThreeWeightVectors σ weight) (hw : w ≠ 0) : LevelThreeCusp σ :=
  ⟨w.val, fun h => hw (Subtype.ext h), (mem_levelThreeWeightVectors.mp w.property).1⟩

/-- **The linear family of sign-twisted level-three Levi cocycles.**  For an inducing datum of odd
degree whose cuspidal representation has a nonzero level-three vector, every level-three vector of
weight `-(n + 3)` has a sign-twisted Levi cocycle datum `E w` (with lifts fixed only by the bad-line
Levi level), and `w ↦ (E w).α` is additive and homogeneous. -/
theorem exists_levelThreeEichlerFamily {n : ℕ} (D : InducingData n) (hodd : Odd n)
    (hσ : LevelThreeCusp D.cusp) :
    ∃ E : levelThreeWeightVectors D.cusp (-((n : ℤ) + 3)) → LineLeviCocycleData3 D.cusp n,
      (∀ w w', (E (w + w')).α = (E w).α + (E w').α) ∧
      (∀ (c : ℂ) w, (E (c • w)).α = c • (E w).α) := by
  obtain ⟨k, hk⟩ := hodd
  have hn : (n : ℤ) = 2 * (k : ℤ) + 1 := by exact_mod_cast hk
  have hw : 2 * (-((k : ℤ) + 2)) = -((n : ℤ) + 3) := by omega
  exact ⟨l3FamilyData D hσ (-((k : ℤ) + 2)) hw (AnalyticClasses.continuousStages D),
    fun w w' => l3FamilyData_α_add D hσ (-((k : ℤ) + 2)) hw (AnalyticClasses.continuousStages D)
      w w',
    fun c w => l3FamilyData_α_smul D hσ (-((k : ℤ) + 2)) hw (AnalyticClasses.continuousStages D)
      c w⟩

/-- **The linear-map form**: the sign-twisted level-three Levi cocycle data `E w` of the level-three
weight vectors of weight `-(n + 3)` have `α` given by a ℂ-linear map `T`. -/
theorem exists_levelThreeEichlerLinear {n : ℕ} (D : InducingData n) (hodd : Odd n)
    (hσ : LevelThreeCusp D.cusp) :
    ∃ (E : levelThreeWeightVectors D.cusp (-((n : ℤ) + 3)) → LineLeviCocycleData3 D.cusp n)
      (T : levelThreeWeightVectors D.cusp (-((n : ℤ) + 3)) →ₗ[ℂ]
        (BinaryRealGL → BinaryAdelicGL → Binary.HomogeneousPoly (n + 1))),
      ∀ w, (E w).α = T w := by
  obtain ⟨k, hk⟩ := hodd
  have hn : (n : ℤ) = 2 * (k : ℤ) + 1 := by exact_mod_cast hk
  have hw : 2 * (-((k : ℤ) + 2)) = -((n : ℤ) + 3) := by omega
  exact ⟨l3FamilyData D hσ (-((k : ℤ) + 2)) hw (AnalyticClasses.continuousStages D),
    l3FamilyMap D hσ (-((k : ℤ) + 2)) hw (AnalyticClasses.continuousStages D),
    fun w => l3FamilyData_α D hσ (-((k : ℤ) + 2)) hw (AnalyticClasses.continuousStages D) w⟩

/-- The same, with the additivity and homogeneity stated pointwise. -/
theorem exists_levelThreeEichlerFamily_apply {n : ℕ} (D : InducingData n) (hodd : Odd n)
    (hσ : LevelThreeCusp D.cusp) :
    ∃ E : levelThreeWeightVectors D.cusp (-((n : ℤ) + 3)) → LineLeviCocycleData3 D.cusp n,
      (∀ w w' g x, (E (w + w')).α g x = (E w).α g x + (E w').α g x) ∧
      (∀ (c : ℂ) w g x, (E (c • w)).α g x = c • (E w).α g x) := by
  obtain ⟨E, hadd, hsmul⟩ := exists_levelThreeEichlerFamily D hodd hσ
  exact ⟨E, fun w w' g x => congrFun (congrFun (hadd w w') g) x,
    fun c w g x => congrFun (congrFun (hsmul c w) g) x⟩

/-- The same, from a nonzero level-three weight vector. -/
theorem exists_levelThreeEichlerFamily_of_ne {n : ℕ} (D : InducingData n) (hodd : Odd n)
    (w₀ : levelThreeWeightVectors D.cusp (-((n : ℤ) + 3))) (hw₀ : w₀ ≠ 0) :
    ∃ E : levelThreeWeightVectors D.cusp (-((n : ℤ) + 3)) → LineLeviCocycleData3 D.cusp n,
      (∀ w w' g x, (E (w + w')).α g x = (E w).α g x + (E w').α g x) ∧
      (∀ (c : ℂ) w g x, (E (c • w)).α g x = c • (E w).α g x) :=
  exists_levelThreeEichlerFamily_apply D hodd (levelThreeCusp_of_weightVector w₀ hw₀)

end TernaryPeriodPolynomials.SourceConstruction

end
