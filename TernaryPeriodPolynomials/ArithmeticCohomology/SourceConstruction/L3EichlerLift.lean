module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.L3EichlerPrimitive
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.L3EichlerData
public import TernaryPeriodPolynomials.ArithmeticCohomology.Twisted.Source.EichlerTwLift
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Source.BadLine

@[expose] public section


/-!
# The level-three sign-twisted Eichler cocycle: scalar realization and packaging

The twisted Hilbert-level cocycle `A ↦ P⁻(A · i)` of a smooth holomorphic weight `-(n + 3)` vector
fixed by the level-three Levi level has smooth components fixed by that level.  Its realization
`L3Input.alpha` is a polynomial-valued function on the adelic group satisfying the sign-twisted
cocycle identity, vanishing on the orthogonal group, with explicit smooth lifts fixed by the
level-three Levi level, real-analytic scalar coefficients and right invariance under the
level-three Levi level.  The result is packaged as `LineLeviCocycleData3`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.SourceConstruction

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.AnalyticClasses
open TernaryPeriodPolynomials.PlaneEisensteinContinuation
open TernaryPeriodPolynomials.TwistedSource
open TernaryPeriodPolynomials.Separation (PlaneLeviLevel)
open TernaryPeriodPolynomials.MultiplicityOne
  (LevelThreeCusp levelThreeValues mem_levelThreeValues)
open scoped Matrix.Norms.Elementwise

/-- The scalar-valued twisted Eichler cocycle of a vector: the realization of the Hilbert-level
cocycle. -/
def l3Alpha (σ : CuspidalRepresentation) (n : ℕ) (halfWeight : ℤ) (v : σ.H) (A : BinaryRealGL) :
    BinaryAdelicGL → Binary.HomogeneousPoly (n + 1) :=
  hilbertLift σ n (l3Cocycle σ n halfWeight v A)

/-- A vector fixed by the level-three Levi level is fixed by the principal congruence level. -/
theorem levelThreeValues_fixedLevel {σ : CuspidalRepresentation} {v : σ.H}
    (hv : v ∈ levelThreeValues σ) :
    v ∈ BinaryLevel.fixedSubspace σ BinaryLevel.finiteCongruence := by
  rintro ⟨element, compact, hcongr, rfl⟩
  have reduced : GeneralLinearGroup.map integralReduction compact = 1 := hcongr
  have in_level : PlaneLeviLevel compact := by
    unfold PlaneLeviLevel
    rw [reduced]
    simp
  exact mem_levelThreeValues.mp hv compact in_level

/-- A vector of the bad-line level subspace is fixed by the principal congruence level. -/
theorem badLevelSubspace_fixedLevel {σ : CuspidalRepresentation} {v : σ.H}
    (hv : v ∈ badLevelSubspace σ) :
    v ∈ BinaryLevel.fixedSubspace σ BinaryLevel.finiteCongruence := by
  apply levelThreeValues_fixedLevel
  rw [LevelThreeSource.levelThreeValues_eq_badLevelSubspace]
  exact hv

namespace L3Input

variable {σ : CuspidalRepresentation} {n : ℕ} (D : L3Input σ n)

theorem fixedLevel : D.vector.val ∈ BinaryLevel.fixedSubspace σ BinaryLevel.finiteCongruence :=
  levelThreeValues_fixedLevel D.vector_level

/-- Every value of the Eichler form is a level-three vector. -/
theorem form_mem_level (w : ℂ) (position : Fin (n + 2)) :
    binaryEndpointHolomorphicForm σ n D.halfWeight D.vector.val w position ∈
      levelThreeValues σ := by
  have orbit : cuspAffineOrbitVector σ D.vector.val w ∈ levelThreeValues σ := by
    unfold cuspAffineOrbitVector
    exact MultiplicityOne.levelThreeValues_real_stable σ _ D.vector.val D.vector_level
  unfold binaryEndpointHolomorphicForm cuspWeightedAffineOrbit
  rw [real_smul_eq_coe (w.im ^ D.halfWeight)]
  exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ orbit)

theorem period_fixed (k : GeneralLinearGroup (Fin 2) IntegralAdeles) (hk : PlaneLeviLevel k)
    (z : ℂ) (hz : 0 < z.im) (position : Fin (n + 2)) :
    σ.π (atFinite (GeneralLinearGroup.map integralEmbedding k))
        (binaryEndpointPeriod σ n D.halfWeight D.vector.val z position) =
      binaryEndpointPeriod σ n D.halfWeight D.vector.val z position := by
  let T := binaryHilbertTranslation (index := Fin (n + 2)) σ
    (atFinite (GeneralLinearGroup.map integralEmbedding k))
  have integrand_fixed : ∀ t : ℝ,
      T ((z - Complex.I) • binaryEndpointHolomorphicForm σ n D.halfWeight D.vector.val
        (Complex.I + t • (z - Complex.I))) =
      (z - Complex.I) • binaryEndpointHolomorphicForm σ n D.halfWeight D.vector.val
        (Complex.I + t • (z - Complex.I)) := by
    intro t
    funext pos
    simp only [T, binaryHilbertTranslation_apply, Pi.smul_apply, map_smul]
    rw [mem_levelThreeValues.mp (D.form_mem_level _ pos) k hk]
  have transported : T (binaryEndpointPeriod σ n D.halfWeight D.vector.val z) =
      binaryEndpointPeriod σ n D.halfWeight D.vector.val z := by
    unfold binaryEndpointPeriod
    rw [← ContinuousLinearMap.intervalIntegral_comp_comm T
      (binaryEndpointPeriod_integrable σ n D.halfWeight D.vector.val z hz)]
    simp only [integrand_fixed]
  exact congrFun transported position

theorem cocycle_smooth (stages : AnalyticScalar.ContinuousStages σ) (A : BinaryRealGL)
    (position : Fin (n + 2)) : D.cocycle A position ∈ σ.smooth := by
  have positive := basePoint_im_pos A
  have reflected_positive : 0 < (binaryComplexReflection (basePoint A)).im := by
    rw [binaryComplexReflection_im]
    exact positive
  have first_smooth := binaryEndpointPeriod_smooth (n := n) σ stages D.halfWeight D.vector
    D.fixedLevel (basePoint A) positive
  have second_smooth := binaryEndpointPeriod_smooth (n := n) σ stages D.halfWeight D.vector
    D.fixedLevel (binaryComplexReflection (basePoint A)) reflected_positive
  have third_smooth := binaryHilbertOperator_smooth σ UpperHalfPlane.J _ second_smooth
  unfold L3Input.cocycle L3Input.potential l3Potential
  exact σ.smooth.smul_mem _ (σ.smooth.sub_mem (first_smooth position) (third_smooth position))

theorem cocycle_fixed (k : GeneralLinearGroup (Fin 2) IntegralAdeles) (hk : PlaneLeviLevel k)
    (A : BinaryRealGL) (position : Fin (n + 2)) :
    σ.π (atFinite (GeneralLinearGroup.map integralEmbedding k)) (D.cocycle A position) =
      D.cocycle A position := by
  have positive := basePoint_im_pos A
  have reflected_positive : 0 < (binaryComplexReflection (basePoint A)).im := by
    rw [binaryComplexReflection_im]
    exact positive
  have second := binaryHilbertOperator_preserves_finiteLevel σ (binaryWeightBasis (n + 1))
    UpperHalfPlane.J (GeneralLinearGroup.map integralEmbedding k)
    (binaryEndpointPeriod σ n D.halfWeight D.vector.val (binaryComplexReflection (basePoint A)))
    (D.period_fixed k hk _ reflected_positive) position
  have first := D.period_fixed k hk (basePoint A) positive position
  unfold L3Input.cocycle L3Input.potential l3Potential
  simp only [Pi.smul_apply, Pi.sub_apply]
  rw [map_smul, map_sub, first, second]

/-- The scalar-valued twisted Eichler cocycle: the realization of the Hilbert-level cocycle. -/
def alpha (A : BinaryRealGL) : BinaryAdelicGL → Binary.HomogeneousPoly (n + 1) :=
  hilbertLift σ n (D.cocycle A)

theorem alpha_eq (A : BinaryRealGL) :
    D.alpha A = l3Alpha σ n D.halfWeight D.vector.val A := rfl

/-- **The twisted cocycle identity for the scalar Eichler cocycle.** -/
theorem alpha_mul (stages : AnalyticScalar.ContinuousStages σ) (g h : BinaryRealGL)
    (x : BinaryAdelicGL) :
    D.alpha (g * h) x = D.alpha g x +
      signDet g • binaryCohomologicalAction n g (D.alpha h) x := by
  have smooth_g := D.cocycle_smooth stages g
  have smooth_h := D.cocycle_smooth stages h
  have transported := binaryHilbertOperator_smooth σ g (D.cocycle h) smooth_h
  have scaled : ∀ position, (signDet g • binaryHilbertOperator σ (binaryWeightBasis (n + 1)) g
      (D.cocycle h)) position ∈ σ.smooth :=
    fun position => σ.smooth.smul_mem _ (transported position)
  unfold L3Input.alpha
  rw [D.cocycle_mul, hilbertLift_add σ _ _ smooth_g scaled, hilbertLift_smul σ _ _ transported,
    hilbertLift_binaryHilbertOperator σ g _ smooth_h]
  rfl

theorem alpha_eq_zero_of_smul_I (A : BinaryRealGL)
    (h : A • UpperHalfPlane.I = UpperHalfPlane.I) (x : BinaryAdelicGL) :
    D.alpha A x = 0 := by
  unfold L3Input.alpha
  rw [D.cocycle_eq_zero_of_smul_I A h]
  exact congrFun (EichlerInput.hilbertLift_zero' (σ := σ) (n := n)) x

/-- **The twisted scalar Eichler cocycle vanishes on every orthogonal matrix.** -/
theorem alpha_orthogonal (k : BinaryRealGL) (hk : k.val.transpose * k.val = 1)
    (x : BinaryAdelicGL) : D.alpha k x = 0 :=
  D.alpha_eq_zero_of_smul_I k (orthogonal_smul_I k hk) x

/-- **Finite level**: the twisted scalar Eichler cocycle is right invariant under the
level-three Levi level. -/
theorem alpha_finiteLevel (stages : AnalyticScalar.ContinuousStages σ)
    (k : GeneralLinearGroup (Fin 2) IntegralAdeles) (hk : PlaneLeviLevel k) (g : BinaryRealGL)
    (x : BinaryAdelicGL) :
    D.alpha g (x * atFinite (GeneralLinearGroup.map integralEmbedding k)) = D.alpha g x := by
  have step : ∀ position : Fin (n + 2),
      smoothRealize σ (D.cocycle g position)
        (x * atFinite (GeneralLinearGroup.map integralEmbedding k)) =
      smoothRealize σ (D.cocycle g position) x := by
    intro position
    rw [smoothRealize_of_mem σ ⟨_, D.cocycle_smooth stages g position⟩]
    have equivariant := σ.equivariant (atFinite (GeneralLinearGroup.map integralEmbedding k))
      ⟨D.cocycle g position, D.cocycle_smooth stages g position⟩ x
    have same : (⟨σ.π (atFinite (GeneralLinearGroup.map integralEmbedding k))
        (D.cocycle g position), σ.smooth_stable _ _ (D.cocycle_smooth stages g position)⟩ :
          σ.smooth) = ⟨D.cocycle g position, D.cocycle_smooth stages g position⟩ :=
      Subtype.ext (D.cocycle_fixed k hk g position)
    rw [← equivariant]
    exact congrArg (fun v : σ.smooth => σ.realize v x) same
  unfold L3Input.alpha hilbertLift
  exact Finset.sum_congr rfl fun position _ => by rw [step position]

/-- **Finite level, bad-line form**: right invariance under every `k ∈ GL₂(ℤ̂)` with `diag(1, k)`
in the finite level. -/
theorem alpha_finiteLevel_badLine (stages : AnalyticScalar.ContinuousStages σ)
    (k : GeneralLinearGroup (Fin 2) IntegralAdeles)
    (hk : GeneralLinearGroup.map integralEmbedding (lineLevi 1 k) ∈ finiteLevel)
    (g : BinaryRealGL) (x : BinaryAdelicGL) :
    D.alpha g (x * atFinite (GeneralLinearGroup.map integralEmbedding k)) = D.alpha g x :=
  D.alpha_finiteLevel stages k ((LevelThreeSource.planeLeviLevel_iff_lineLevi_mem k).mpr hk)
    g x

/-- The scalar twisted Eichler cocycle is the pointwise twisted Eichler normal form. -/
theorem alpha_eq_eichlerNormalTw (stages : AnalyticScalar.ContinuousStages σ)
    (A : BinaryRealGL) :
    D.alpha A = eichlerNormalTw n (endpointScalar σ D.halfWeight D.vector) A := by
  have positive := basePoint_im_pos A
  have reflected_positive : 0 < (binaryComplexReflection (basePoint A)).im := by
    rw [binaryComplexReflection_im]
    exact positive
  have first_smooth := binaryEndpointPeriod_smooth (n := n) σ stages D.halfWeight D.vector
    D.fixedLevel (basePoint A) positive
  have second_smooth := binaryEndpointPeriod_smooth (n := n) σ stages D.halfWeight D.vector
    D.fixedLevel (binaryComplexReflection (basePoint A)) reflected_positive
  have third_smooth := binaryHilbertOperator_smooth σ UpperHalfPlane.J _ second_smooth
  have diff_smooth : ∀ position, (binaryEndpointPeriod σ n D.halfWeight D.vector.val (basePoint A) -
      binaryHilbertOperator σ (binaryWeightBasis (n + 1)) UpperHalfPlane.J
        (binaryEndpointPeriod σ n D.halfWeight D.vector.val
          (binaryComplexReflection (basePoint A)))) position ∈ σ.smooth :=
    fun position => σ.smooth.sub_mem (first_smooth position) (third_smooth position)
  unfold L3Input.alpha L3Input.cocycle L3Input.potential l3Potential
  rw [hilbertLift_smul σ _ _ diff_smooth, hilbertLift_sub σ _ _ first_smooth third_smooth,
    hilbertLift_binaryHilbertOperator σ UpperHalfPlane.J _ second_smooth,
    hilbertLift_binaryEndpointPeriod σ stages D.halfWeight D.vector D.fixedLevel _ positive,
    hilbertLift_binaryEndpointPeriod σ stages D.halfWeight D.vector D.fixedLevel _
      reflected_positive]
  rfl

/-- **Scalar analyticity.** Every coefficient of the twisted Eichler cocycle is a real-analytic
function of the real group element, at each fixed adelic point. -/
theorem alpha_scalar_smooth (stages : AnalyticScalar.ContinuousStages σ)
    (m : Fin 2 →₀ ℕ) (A : BinaryAdelicGL) :
    Smooth (fun x : Fin 1 → BinaryRealGL => (D.alpha (x 0) A).val.coeff m) := by
  have holomorphic : ∀ h, DifferentiableOn ℂ (endpointScalar σ D.halfWeight D.vector h)
      {z : ℂ | 0 < z.im} := fun h =>
    MultiplicityOne.cuspScalarWeightedRealization_holomorphic σ D.halfWeight D.vector
      D.vector_level D.rotation D.holomorphic h
  have regular := eichlerNormalTw_functional_smooth (n := n)
    (endpointScalar σ D.halfWeight D.vector) holomorphic A (coeffFunctional (n := n) m)
  unfold Smooth at regular ⊢
  refine regular.congr (fun point _ => ?_)
  exact congrArg (fun p : Binary.HomogeneousPoly (n + 1) => p.val.coeff m)
    (congrFun (D.alpha_eq_eichlerNormalTw stages (invertibleMatrix (point 0))) A)

/-- The Hilbert-level twisted cocycle is real analytic in the group element. -/
theorem cocycle_smoothFamily :
    Smooth (fun point : Fin 1 → BinaryRealGL => D.cocycle (point 0)) := by
  have period := endpointPeriod_contDiffOn σ n D.halfWeight D.vector
  have base : ContDiffOn ℝ ⊤ (fun point : Fin 1 → Matrix (Fin 2) (Fin 2) ℝ =>
      basePoint (invertibleMatrix (point 0))) {point | ∀ position, (point position).det ≠ 0} :=
    basePoint_contDiffOn.comp (contDiff_apply ℝ (Matrix (Fin 2) (Fin 2) ℝ) (0 : Fin 1)).contDiffOn
      (fun _ member => member 0)
  have reflected : ContDiffOn ℝ ⊤ (fun point : Fin 1 → Matrix (Fin 2) (Fin 2) ℝ =>
      binaryComplexReflection (basePoint (invertibleMatrix (point 0))))
      {point | ∀ position, (point position).det ≠ 0} :=
    binaryComplexReflection.contDiff.comp_contDiffOn base
  have first := period.comp base (fun point _ => basePoint_im_pos (invertibleMatrix (point 0)))
  have second := period.comp reflected (fun point _ => by
    change 0 < (binaryComplexReflection (basePoint (invertibleMatrix (point 0)))).im
    rw [binaryComplexReflection_im]
    exact basePoint_im_pos _)
  have third := ((binaryHilbertOperator σ (binaryWeightBasis (n + 1))
    UpperHalfPlane.J).restrictScalars ℝ).contDiff.comp_contDiffOn second
  exact (first.sub third).const_smul (2 : ℂ)⁻¹

/-- The smooth lift of a monomial coefficient of the twisted Eichler cocycle. -/
def liftVector (stages : AnalyticScalar.ContinuousStages σ) (m : Fin 2 →₀ ℕ)
    (g : BinaryRealGL) : σ.smooth :=
  ∑ position, ((binaryWeightBasis (n + 1) position).val.coeff m) •
    (⟨D.cocycle g position, D.cocycle_smooth stages g position⟩ : σ.smooth)

theorem liftVector_realize (stages : AnalyticScalar.ContinuousStages σ) (m : Fin 2 →₀ ℕ)
    (g : BinaryRealGL) (A : BinaryAdelicGL) :
    σ.realize (D.liftVector stages m g) A = (D.alpha g A).val.coeff m := by
  unfold L3Input.liftVector L3Input.alpha hilbertLift
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Submodule.coe_sum,
    Submodule.coe_smul, MvPolynomial.coeff_sum, MvPolynomial.coeff_smul]
  refine Finset.sum_congr rfl fun position _ => ?_
  rw [smoothRealize_of_mem σ ⟨_, D.cocycle_smooth stages g position⟩, mul_comm]

theorem liftVector_smooth (stages : AnalyticScalar.ContinuousStages σ) (m : Fin 2 →₀ ℕ) :
    Smooth (fun x : Fin 1 → BinaryRealGL => (D.liftVector stages m (x 0)).val) := by
  have normal := D.cocycle_smoothFamily
  unfold Smooth at normal ⊢
  have components : ∀ position, ContDiffOn ℝ ⊤
      (fun point : Fin 1 → Matrix (Fin 2) (Fin 2) ℝ =>
        D.cocycle (invertibleMatrix (point 0)) position)
      {point | ∀ position, (point position).det ≠ 0} := fun position =>
    contDiffOn_pi.mp normal position
  refine ContDiffOn.congr (f := fun point : Fin 1 → Matrix (Fin 2) (Fin 2) ℝ =>
    ∑ position, ((binaryWeightBasis (n + 1) position).val.coeff m) •
      D.cocycle (invertibleMatrix (point 0)) position) ?_
    (fun point _ => ?_)
  · exact ContDiffOn.sum fun position _ => (components position).const_smul _
  · unfold L3Input.liftVector
    simp only [Submodule.coe_sum, Submodule.coe_smul]

theorem liftVector_level (stages : AnalyticScalar.ContinuousStages σ) (m : Fin 2 →₀ ℕ)
    (g : BinaryRealGL) : (D.liftVector stages m g).val ∈ levelThreeValues σ := by
  unfold L3Input.liftVector
  rw [Submodule.coe_sum]
  refine Submodule.sum_mem _ fun position _ => ?_
  rw [Submodule.coe_smul]
  exact Submodule.smul_mem _ _
    (mem_levelThreeValues.mpr fun k hk => D.cocycle_fixed k hk g position)

theorem alpha_binaryValues (stages : AnalyticScalar.ContinuousStages σ)
    (g : BinaryRealGL) : BinaryValues σ n (D.alpha g) := by
  intro m
  refine ⟨D.liftVector stages m g, ?_⟩
  funext A
  exact D.liftVector_realize stages m g A

/-- **The level-three line Levi cocycle datum of an Eichler input**: the sign-twisted Eichler
cocycle `A ↦ ½ (Per(A i) - J Per(-conj(A i)))` with its regularity package. -/
def toData (stages : AnalyticScalar.ContinuousStages σ) : LineLeviCocycleData3 σ n where
  α := D.alpha
  cocycle := fun g h x => D.alpha_mul stages g h x
  orth := fun k hk x => D.alpha_orthogonal k hk x
  lift := D.liftVector stages
  lift_realize := fun μ g A => D.liftVector_realize stages μ g A
  lift_smooth := fun μ => D.liftVector_smooth stages μ
  scalar_smooth := fun μ A => D.alpha_scalar_smooth stages μ A
  levelFixed := fun μ g => by
    have member := D.liftVector_level stages μ g
    rwa [LevelThreeSource.levelThreeValues_eq_badLevelSubspace] at member

theorem toData_α (stages : AnalyticScalar.ContinuousStages σ) :
    (D.toData stages).α = D.alpha := rfl

end L3Input

end TernaryPeriodPolynomials.SourceConstruction

end
