module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Even.WtL3PlaneA
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Even.WtL3TwLiftA
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Even.WtScalarHolomorphic
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Source.GoodPlaneSourceData
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Eichler.Regular

@[expose] public section


/-!
# The weight-generic level-three Eichler cocycle: scalar realization and packaging

Formalized by Claude Sonnet 5.5 (AxiomCode).

Twin of `AxiomCodeLevelThreeSource/LevelThreeEichlerLift` for an integer rotation weight
`wt = -(n + 3)`, so that the odd weights of even degree `n` are covered.  The Hilbert-level cocycle
`A ↦ P⁺(A · i)` of a smooth holomorphic weight `wt` vector fixed by the level-three Levi level has
smooth components fixed by that level.  Its realization `lteAWt` is a polynomial-valued function on
the adelic group satisfying the cocycle identity, vanishing on the orthogonal group, with explicit
smooth lifts in `levelThreeValues` and real-analytic scalar coefficients.  The result is packaged
as `GoodPlaneSourceData.LevelLeviCocycleData` (`lteDataWt`).
-/

noncomputable section

namespace TernaryPeriodPolynomials.EvenLevelThree

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.AnalyticClasses
open TernaryPeriodPolynomials.PlaneEisensteinContinuation
open TernaryPeriodPolynomials.SourceConstruction
  (coeffFunctional eichlerNormal_functional_smooth orthogonal_smul_I)
open TernaryPeriodPolynomials.LevelThreeSource (LevelLeviCocycleData)
open TernaryPeriodPolynomials.Separation (PlaneLeviLevel)
open TernaryPeriodPolynomials.MultiplicityOne
  (levelThreeValues mem_levelThreeValues)
open scoped Matrix.Norms.Elementwise

/-- The scalar-valued Eichler cocycle of a vector, for an integer rotation weight: the
realization of the Hilbert-level cocycle. -/
def lteAlphaWt (σ : CuspidalRepresentation) (n : ℕ) (wt : ℤ) (v : σ.H) (A : BinaryRealGL) :
    BinaryAdelicGL → Binary.HomogeneousPoly (n + 1) :=
  hilbertLift σ n (l3PlaneCocycleWt σ n wt v A)

section Lift

variable {σ : CuspidalRepresentation} {n : ℕ} (D : L3InputWt σ n)

/-- The Hilbert-level Eichler cocycle of the input vector of `D`. -/
def lteCocWt (A : BinaryRealGL) : Fin (n + 2) → σ.H :=
  l3PlaneCocycleWt σ n D.wt D.vector.val A

theorem lteCocWt_eq (A : BinaryRealGL) : lteCocWt D A = D.planeCocycle A := rfl

/-- **The cocycle identity.** -/
theorem lteCocWt_mul (A B : BinaryRealGL) :
    lteCocWt D (A * B) = lteCocWt D A +
      binaryHilbertOperator σ (binaryWeightBasis (n + 1)) A (lteCocWt D B) :=
  D.planeCocycle_mul A B

/-- **The cocycle vanishes on the stabilizer of `i`.** -/
theorem lteCocWt_eq_zero_of_smul_I (A : BinaryRealGL)
    (h : A • UpperHalfPlane.I = UpperHalfPlane.I) : lteCocWt D A = 0 :=
  D.planeCocycle_eq_zero_of_smul_I A h

theorem lteCocWt_smooth (stages : AnalyticScalar.ContinuousStages σ) (A : BinaryRealGL)
    (position : Fin (n + 2)) : lteCocWt D A position ∈ σ.smooth := by
  have positive := basePoint_im_pos A
  have reflected_positive : 0 < (binaryComplexReflection (basePoint A)).im := by
    rw [binaryComplexReflection_im]
    exact positive
  have first_smooth := binaryEndpointPeriod_smoothWt (n := n) σ stages D.wt D.vector
    D.fixedLevel (basePoint A) positive
  have second_smooth := binaryEndpointPeriod_smoothWt (n := n) σ stages D.wt D.vector
    D.fixedLevel (binaryComplexReflection (basePoint A)) reflected_positive
  have third_smooth := binaryHilbertOperator_smooth σ UpperHalfPlane.J _ second_smooth
  unfold lteCocWt l3PlaneCocycleWt l3PlanePotentialWt
  exact σ.smooth.smul_mem _ (σ.smooth.add_mem (first_smooth position) (third_smooth position))

theorem lteCocWt_fixed (k : GeneralLinearGroup (Fin 2) IntegralAdeles) (hk : PlaneLeviLevel k)
    (A : BinaryRealGL) (position : Fin (n + 2)) :
    σ.π (atFinite (GeneralLinearGroup.map integralEmbedding k)) (lteCocWt D A position) =
      lteCocWt D A position := by
  have positive := basePoint_im_pos A
  have reflected_positive : 0 < (binaryComplexReflection (basePoint A)).im := by
    rw [binaryComplexReflection_im]
    exact positive
  have second := binaryHilbertOperator_preserves_finiteLevel σ (binaryWeightBasis (n + 1))
    UpperHalfPlane.J (GeneralLinearGroup.map integralEmbedding k)
    (binaryEndpointPeriodWt σ n D.wt D.vector.val (binaryComplexReflection (basePoint A)))
    (D.period_fixed k hk _ reflected_positive) position
  have first := D.period_fixed k hk (basePoint A) positive position
  unfold lteCocWt l3PlaneCocycleWt l3PlanePotentialWt
  simp only [Pi.smul_apply, Pi.add_apply]
  rw [map_smul, map_add, first, second]

/-- The scalar-valued Eichler cocycle of the input vector of `D`: the realization of the
Hilbert-level cocycle. -/
def lteAWt (A : BinaryRealGL) : BinaryAdelicGL → Binary.HomogeneousPoly (n + 1) :=
  hilbertLift σ n (lteCocWt D A)

theorem lteAWt_eq (A : BinaryRealGL) :
    lteAWt D A = lteAlphaWt σ n D.wt D.vector.val A := rfl

/-- **The cocycle identity for the scalar Eichler cocycle.** -/
theorem lteA_mulWt (stages : AnalyticScalar.ContinuousStages σ) (g h : BinaryRealGL)
    (x : BinaryAdelicGL) :
    lteAWt D (g * h) x = lteAWt D g x + binaryCohomologicalAction n g (lteAWt D h) x := by
  have smooth_g := lteCocWt_smooth D stages g
  have smooth_h := lteCocWt_smooth D stages h
  have transported := binaryHilbertOperator_smooth σ g (lteCocWt D h) smooth_h
  unfold lteAWt
  rw [lteCocWt_mul, hilbertLift_add σ _ _ smooth_g transported,
    hilbertLift_binaryHilbertOperator σ g _ smooth_h]
  rfl

theorem lteA_eq_zero_of_smul_IWt (A : BinaryRealGL)
    (h : A • UpperHalfPlane.I = UpperHalfPlane.I) (x : BinaryAdelicGL) :
    lteAWt D A x = 0 := by
  unfold lteAWt
  rw [lteCocWt_eq_zero_of_smul_I D A h]
  exact congrFun
    (SourceConstruction.EichlerInput.hilbertLift_zero' (σ := σ) (n := n)) x

/-- **The scalar Eichler cocycle vanishes on every orthogonal matrix.** -/
theorem lteA_orthogonalWt (k : BinaryRealGL) (hk : k.val.transpose * k.val = 1)
    (x : BinaryAdelicGL) : lteAWt D k x = 0 :=
  lteA_eq_zero_of_smul_IWt D k (orthogonal_smul_I k hk) x

/-- **Finite level**: the scalar Eichler cocycle is right invariant under the level-three Levi
level. -/
theorem lteA_finiteLevelWt (stages : AnalyticScalar.ContinuousStages σ)
    (k : GeneralLinearGroup (Fin 2) IntegralAdeles) (hk : PlaneLeviLevel k) (g : BinaryRealGL)
    (x : BinaryAdelicGL) :
    lteAWt D g (x * atFinite (GeneralLinearGroup.map integralEmbedding k)) = lteAWt D g x := by
  have step : ∀ position : Fin (n + 2),
      smoothRealize σ (lteCocWt D g position)
        (x * atFinite (GeneralLinearGroup.map integralEmbedding k)) =
      smoothRealize σ (lteCocWt D g position) x := by
    intro position
    rw [smoothRealize_of_mem σ ⟨_, lteCocWt_smooth D stages g position⟩]
    have equivariant := σ.equivariant (atFinite (GeneralLinearGroup.map integralEmbedding k))
      ⟨lteCocWt D g position, lteCocWt_smooth D stages g position⟩ x
    have same : (⟨σ.π (atFinite (GeneralLinearGroup.map integralEmbedding k))
        (lteCocWt D g position), σ.smooth_stable _ _ (lteCocWt_smooth D stages g position)⟩ :
          σ.smooth) = ⟨lteCocWt D g position, lteCocWt_smooth D stages g position⟩ :=
      Subtype.ext (lteCocWt_fixed D k hk g position)
    rw [← equivariant]
    exact congrArg (fun v : σ.smooth => σ.realize v x) same
  unfold lteAWt hilbertLift
  exact Finset.sum_congr rfl fun position _ => by rw [step position]

/-- The scalar Eichler cocycle is the pointwise Eichler normal form. -/
theorem lteA_eq_eichlerNormalWt (stages : AnalyticScalar.ContinuousStages σ) (A : BinaryRealGL) :
    lteAWt D A = eichlerNormal n (endpointScalarWt σ D.wt D.vector) A := by
  have positive := basePoint_im_pos A
  have reflected_positive : 0 < (binaryComplexReflection (basePoint A)).im := by
    rw [binaryComplexReflection_im]
    exact positive
  have first_smooth := binaryEndpointPeriod_smoothWt (n := n) σ stages D.wt D.vector
    D.fixedLevel (basePoint A) positive
  have second_smooth := binaryEndpointPeriod_smoothWt (n := n) σ stages D.wt D.vector
    D.fixedLevel (binaryComplexReflection (basePoint A)) reflected_positive
  have third_smooth := binaryHilbertOperator_smooth σ UpperHalfPlane.J _ second_smooth
  have sum_smooth : ∀ position, (binaryEndpointPeriodWt σ n D.wt D.vector.val (basePoint A) +
      binaryHilbertOperator σ (binaryWeightBasis (n + 1)) UpperHalfPlane.J
        (binaryEndpointPeriodWt σ n D.wt D.vector.val
          (binaryComplexReflection (basePoint A)))) position ∈ σ.smooth :=
    fun position => σ.smooth.add_mem (first_smooth position) (third_smooth position)
  unfold lteAWt lteCocWt l3PlaneCocycleWt l3PlanePotentialWt
  rw [hilbertLift_smul σ _ _ sum_smooth, hilbertLift_add σ _ _ first_smooth third_smooth,
    hilbertLift_binaryHilbertOperator σ UpperHalfPlane.J _ second_smooth,
    hilbertLift_binaryEndpointPeriodWt σ stages D.wt D.vector D.fixedLevel _ positive,
    hilbertLift_binaryEndpointPeriodWt σ stages D.wt D.vector D.fixedLevel _
      reflected_positive]
  rfl

/-- **Scalar analyticity.** Every coefficient of the Eichler cocycle is a real-analytic function
of the real group element, at each fixed adelic point. -/
theorem lteA_scalar_smoothWt (stages : AnalyticScalar.ContinuousStages σ)
    (m : Fin 2 →₀ ℕ) (A : BinaryAdelicGL) :
    Smooth (fun x : Fin 1 → BinaryRealGL => (lteAWt D (x 0) A).val.coeff m) := by
  have holomorphic : ∀ h, DifferentiableOn ℂ (endpointScalarWt σ D.wt D.vector h)
      {z : ℂ | 0 < z.im} := fun h =>
    cuspScalarWeightedRealization_holomorphicWt σ stages D.wt D.vector D.fixedLevel
      D.holomorphic h
  have regular := eichlerNormal_functional_smooth (n := n)
    (endpointScalarWt σ D.wt D.vector) holomorphic A (coeffFunctional (n := n) m)
  unfold Smooth at regular ⊢
  refine regular.congr (fun point _ => ?_)
  exact congrArg (fun p : Binary.HomogeneousPoly (n + 1) => p.val.coeff m)
    (congrFun (lteA_eq_eichlerNormalWt D stages (invertibleMatrix (point 0))) A)

/-- The Hilbert-level cocycle is real analytic in the group element. -/
theorem lteCoc_smoothFamilyWt :
    Smooth (fun point : Fin 1 → BinaryRealGL => lteCocWt D (point 0)) := by
  have period := endpointPeriod_contDiffOnWt σ n D.wt D.vector
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
  exact (first.add third).const_smul (2 : ℂ)⁻¹

/-- The smooth lift of a monomial coefficient of the Eichler cocycle. -/
def lteLiftWt (stages : AnalyticScalar.ContinuousStages σ) (m : Fin 2 →₀ ℕ)
    (g : BinaryRealGL) : σ.smooth :=
  ∑ position, ((binaryWeightBasis (n + 1) position).val.coeff m) •
    (⟨lteCocWt D g position, lteCocWt_smooth D stages g position⟩ : σ.smooth)

theorem lteLift_realizeWt (stages : AnalyticScalar.ContinuousStages σ) (m : Fin 2 →₀ ℕ)
    (g : BinaryRealGL) (A : BinaryAdelicGL) :
    σ.realize (lteLiftWt D stages m g) A = (lteAWt D g A).val.coeff m := by
  unfold lteLiftWt lteAWt hilbertLift
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Submodule.coe_sum,
    Submodule.coe_smul, MvPolynomial.coeff_sum, MvPolynomial.coeff_smul]
  refine Finset.sum_congr rfl fun position _ => ?_
  rw [smoothRealize_of_mem σ ⟨_, lteCocWt_smooth D stages g position⟩, mul_comm]

theorem lteLift_smoothWt (stages : AnalyticScalar.ContinuousStages σ) (m : Fin 2 →₀ ℕ) :
    Smooth (fun x : Fin 1 → BinaryRealGL => (lteLiftWt D stages m (x 0)).val) := by
  have normal := lteCoc_smoothFamilyWt D
  unfold Smooth at normal ⊢
  have components : ∀ position, ContDiffOn ℝ ⊤
      (fun point : Fin 1 → Matrix (Fin 2) (Fin 2) ℝ =>
        lteCocWt D (invertibleMatrix (point 0)) position)
      {point | ∀ position, (point position).det ≠ 0} := fun position =>
    contDiffOn_pi.mp normal position
  refine ContDiffOn.congr (f := fun point : Fin 1 → Matrix (Fin 2) (Fin 2) ℝ =>
    ∑ position, ((binaryWeightBasis (n + 1) position).val.coeff m) •
      lteCocWt D (invertibleMatrix (point 0)) position) ?_
    (fun point _ => ?_)
  · exact ContDiffOn.sum fun position _ => (components position).const_smul _
  · unfold lteLiftWt
    simp only [Submodule.coe_sum, Submodule.coe_smul]

theorem lteLift_levelWt (stages : AnalyticScalar.ContinuousStages σ) (m : Fin 2 →₀ ℕ)
    (g : BinaryRealGL) : (lteLiftWt D stages m g).val ∈ levelThreeValues σ := by
  unfold lteLiftWt
  rw [Submodule.coe_sum]
  refine Submodule.sum_mem _ fun position _ => ?_
  rw [Submodule.coe_smul]
  exact Submodule.smul_mem _ _
    (mem_levelThreeValues.mpr fun k hk => lteCocWt_fixed D k hk g position)

/-- **The level-three Levi cocycle datum of an Eichler input**: the Eichler cocycle
`A ↦ ½ (Per(A i) + J Per(-conj(A i)))` with its regularity package. -/
def lteDataWt (stages : AnalyticScalar.ContinuousStages σ) : LevelLeviCocycleData σ n where
  α := lteAWt D
  cocycle := fun g h x => lteA_mulWt D stages g h x
  orth := fun k hk x => lteA_orthogonalWt D k hk x
  lift := lteLiftWt D stages
  lift_realize := fun μ g A => lteLift_realizeWt D stages μ g A
  lift_smooth := fun μ => lteLift_smoothWt D stages μ
  scalar_smooth := fun μ A => lteA_scalar_smoothWt D stages μ A
  level := fun μ g => lteLift_levelWt D stages μ g

theorem lteData_αWt (stages : AnalyticScalar.ContinuousStages σ) :
    (lteDataWt D stages).α = lteAWt D := rfl

end Lift

end TernaryPeriodPolynomials.EvenLevelThree

end
