module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Eichler.Cocycle
public import TernaryPeriodPolynomials.ArithmeticCohomology.Twisted.Source.EichlerTwPrimitive

@[expose] public section


/-!
# The sign-twisted Eichler cocycle: scalar realization and packaging

The twisted Hilbert-level cocycle `A ↦ P⁻(A · i)` has smooth, finite-level-fixed components.  Its
realization `eichlerCocycleTw` is a polynomial-valued function on the adelic group satisfying the
cocycle identity `α (g h) = α g + sign(det g) • (g · α h)`, vanishing on the orthogonal group,
with explicit smooth spherical lifts, real-analytic scalar coefficients and right `GL₂(Ẑ)`
invariance.  This is the twisted analogue of the Eichler construction for the odd quadratic
character.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.TwistedSource

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.AnalyticClasses
open TernaryPeriodPolynomials.PlaneEisensteinContinuation
open TernaryPeriodPolynomials.SourceConstruction
open scoped Matrix.Norms.Elementwise

section Lift

variable {σ : CuspidalRepresentation} {n : ℕ} (D : EichlerInput σ n)

theorem cocycleTw_smooth (stages : AnalyticScalar.ContinuousStages σ) (A : BinaryRealGL)
    (position : Fin (n + 2)) : cocycleTw D A position ∈ σ.smooth := by
  have positive := basePoint_im_pos A
  have reflected_positive : 0 < (binaryComplexReflection (basePoint A)).im := by
    rw [binaryComplexReflection_im]
    exact positive
  have first_smooth := binaryEndpointPeriod_smooth (n := n) σ stages D.halfWeight D.vector
    D.fixedLevel (basePoint A) positive
  have second_smooth := binaryEndpointPeriod_smooth (n := n) σ stages D.halfWeight D.vector
    D.fixedLevel (binaryComplexReflection (basePoint A)) reflected_positive
  have third_smooth := binaryHilbertOperator_smooth σ UpperHalfPlane.J _ second_smooth
  unfold cocycleTw potentialTw
  exact σ.smooth.smul_mem _ (σ.smooth.sub_mem (first_smooth position) (third_smooth position))

theorem cocycleTw_fixed (k : GeneralLinearGroup (Fin 2) IntegralAdeles) (A : BinaryRealGL)
    (position : Fin (n + 2)) :
    σ.π (atFinite (GeneralLinearGroup.map integralEmbedding k)) (cocycleTw D A position) =
      cocycleTw D A position := by
  have positive := basePoint_im_pos A
  have reflected_positive : 0 < (binaryComplexReflection (basePoint A)).im := by
    rw [binaryComplexReflection_im]
    exact positive
  have second := binaryHilbertOperator_preserves_finiteLevel σ (binaryWeightBasis (n + 1))
    UpperHalfPlane.J (GeneralLinearGroup.map integralEmbedding k)
    (binaryEndpointPeriod σ n D.halfWeight D.vector.val (binaryComplexReflection (basePoint A)))
    (D.period_fixed k _ reflected_positive) position
  have first := D.period_fixed k (basePoint A) positive position
  unfold cocycleTw potentialTw
  simp only [Pi.smul_apply, Pi.sub_apply]
  rw [map_smul, map_sub, first, second]

/-- The scalar-valued twisted Eichler cocycle: the realization of the Hilbert-level cocycle. -/
def eichlerCocycleTw (A : BinaryRealGL) : BinaryAdelicGL → Binary.HomogeneousPoly (n + 1) :=
  hilbertLift σ n (cocycleTw D A)

/-- **The twisted cocycle identity for the scalar Eichler cocycle.** -/
theorem eichlerCocycleTw_mul (stages : AnalyticScalar.ContinuousStages σ) (g h : BinaryRealGL)
    (x : BinaryAdelicGL) :
    eichlerCocycleTw D (g * h) x = eichlerCocycleTw D g x +
      signDet g • binaryCohomologicalAction n g (eichlerCocycleTw D h) x := by
  have smooth_g := cocycleTw_smooth D stages g
  have smooth_h := cocycleTw_smooth D stages h
  have transported := binaryHilbertOperator_smooth σ g (cocycleTw D h) smooth_h
  have scaled : ∀ position, (signDet g • binaryHilbertOperator σ (binaryWeightBasis (n + 1)) g
      (cocycleTw D h)) position ∈ σ.smooth :=
    fun position => σ.smooth.smul_mem _ (transported position)
  unfold eichlerCocycleTw
  rw [cocycleTw_mul, hilbertLift_add σ _ _ smooth_g scaled, hilbertLift_smul σ _ _ transported,
    hilbertLift_binaryHilbertOperator σ g _ smooth_h]
  rfl

theorem eichlerCocycleTw_eq_zero_of_smul_I (A : BinaryRealGL)
    (h : A • UpperHalfPlane.I = UpperHalfPlane.I) (x : BinaryAdelicGL) :
    eichlerCocycleTw D A x = 0 := by
  unfold eichlerCocycleTw
  rw [cocycleTw_eq_zero_of_smul_I D A h]
  exact congrFun (EichlerInput.hilbertLift_zero' (σ := σ) (n := n)) x

/-- **The twisted scalar Eichler cocycle vanishes on every orthogonal matrix.** -/
theorem eichlerCocycleTw_orthogonal (k : BinaryRealGL) (hk : k.val.transpose * k.val = 1)
    (x : BinaryAdelicGL) : eichlerCocycleTw D k x = 0 :=
  eichlerCocycleTw_eq_zero_of_smul_I D k (orthogonal_smul_I k hk) x

/-- **Finite level**: the twisted scalar Eichler cocycle is right invariant under `GL₂(Ẑ)`. -/
theorem eichlerCocycleTw_finiteLevel (stages : AnalyticScalar.ContinuousStages σ)
    (k : GeneralLinearGroup (Fin 2) IntegralAdeles) (g : BinaryRealGL) (x : BinaryAdelicGL) :
    eichlerCocycleTw D g (x * atFinite (GeneralLinearGroup.map integralEmbedding k)) =
      eichlerCocycleTw D g x := by
  have step : ∀ position : Fin (n + 2),
      smoothRealize σ (cocycleTw D g position)
        (x * atFinite (GeneralLinearGroup.map integralEmbedding k)) =
      smoothRealize σ (cocycleTw D g position) x := by
    intro position
    rw [smoothRealize_of_mem σ ⟨_, cocycleTw_smooth D stages g position⟩]
    have equivariant := σ.equivariant (atFinite (GeneralLinearGroup.map integralEmbedding k))
      ⟨cocycleTw D g position, cocycleTw_smooth D stages g position⟩ x
    have same : (⟨σ.π (atFinite (GeneralLinearGroup.map integralEmbedding k))
        (cocycleTw D g position), σ.smooth_stable _ _ (cocycleTw_smooth D stages g position)⟩ :
          σ.smooth) = ⟨cocycleTw D g position, cocycleTw_smooth D stages g position⟩ :=
      Subtype.ext (cocycleTw_fixed D k g position)
    rw [← equivariant]
    exact congrArg (fun v : σ.smooth => σ.realize v x) same
  unfold eichlerCocycleTw hilbertLift
  exact Finset.sum_congr rfl fun position _ => by rw [step position]

end Lift

section Scalar

variable {n : ℕ}

/-- The pointwise twisted Eichler normal form `½ (Per(A·i) - J Per(-conj(A·i)))`. -/
def eichlerNormalTw (n : ℕ) (F : BinaryAdelicGL → ℂ → ℂ) (A : BinaryRealGL)
    (h : BinaryAdelicGL) : Binary.HomogeneousPoly (n + 1) :=
  (2 : ℂ)⁻¹ • (eichlerPeriod n F (basePoint A) h -
    binaryAmbientRepresentation n UpperHalfPlane.J
      (eichlerPeriod n F (binaryComplexReflection (basePoint A))) h)

theorem eichler_functional_eichlerNormalTw (F : BinaryAdelicGL → ℂ → ℂ)
    (functional : Binary.HomogeneousPoly (n + 1) →ₗ[ℂ] ℂ) (A : BinaryRealGL)
    (h : BinaryAdelicGL) :
    functional (eichlerNormalTw n F A h) = (2 : ℂ)⁻¹ *
      (functional (eichlerPeriod n F (basePoint A) h) -
        eichlerReflectedFunctional functional (eichlerPeriod n F
          (binaryComplexReflection (basePoint A)) (h * atInfinity UpperHalfPlane.J))) := by
  unfold eichlerNormalTw
  rw [map_smul, map_sub, smul_eq_mul]
  rfl

/-- **Real analyticity of the functionals of the pointwise twisted Eichler normal form.** -/
theorem eichlerNormalTw_functional_smooth (F : BinaryAdelicGL → ℂ → ℂ)
    (holomorphic : ∀ h, DifferentiableOn ℂ (F h) {z : ℂ | 0 < z.im}) (h : BinaryAdelicGL)
    (functional : Binary.HomogeneousPoly (n + 1) →ₗ[ℂ] ℂ) :
    Smooth (fun x : Fin 1 → BinaryRealGL => functional (eichlerNormalTw n F (x 0) h)) := by
  have base : ContDiffOn ℝ ⊤
      (fun point : Fin 1 → Matrix (Fin 2) (Fin 2) ℝ => basePoint (invertibleMatrix (point 0)))
      {point | ∀ position, (point position).det ≠ 0} :=
    basePoint_contDiffOn.comp (contDiff_apply ℝ (Matrix (Fin 2) (Fin 2) ℝ) (0 : Fin 1)).contDiffOn
      (fun _ member => member 0)
  have reflected : ContDiffOn ℝ ⊤
      (fun point : Fin 1 → Matrix (Fin 2) (Fin 2) ℝ =>
        binaryComplexReflection (basePoint (invertibleMatrix (point 0))))
      {point | ∀ position, (point position).det ≠ 0} :=
    binaryComplexReflection.contDiff.comp_contDiffOn base
  have direct : ∀ (h' : BinaryAdelicGL) (j : Fin (n + 2)), ContDiffOn ℝ ⊤
      (fun point : Fin 1 → Matrix (Fin 2) (Fin 2) ℝ => (binaryWeightBasis (n + 1)).coord j
        (eichlerPeriod n F (basePoint (invertibleMatrix (point 0))) h'))
      {point | ∀ position, (point position).det ≠ 0} := fun h' j =>
    (coordPeriod_contDiffOn F holomorphic h' j).comp base
      (fun point _ => basePoint_im_pos _)
  have mirrored : ∀ (h' : BinaryAdelicGL) (j : Fin (n + 2)), ContDiffOn ℝ ⊤
      (fun point : Fin 1 → Matrix (Fin 2) (Fin 2) ℝ => (binaryWeightBasis (n + 1)).coord j
        (eichlerPeriod n F (binaryComplexReflection (basePoint (invertibleMatrix (point 0)))) h'))
      {point | ∀ position, (point position).det ≠ 0} := fun h' j =>
    (coordPeriod_contDiffOn F holomorphic h' j).comp reflected (fun point _ => by
      change 0 < (binaryComplexReflection (basePoint (invertibleMatrix (point 0)))).im
      rw [binaryComplexReflection_im]
      exact basePoint_im_pos _)
  have expansion : ∀ A : BinaryRealGL, functional (eichlerNormalTw n F A h) = (2 : ℂ)⁻¹ *
      (∑ j, (binaryWeightBasis (n + 1)).coord j (eichlerPeriod n F (basePoint A) h) *
          functional (binaryWeightBasis (n + 1) j) -
        ∑ j, (binaryWeightBasis (n + 1)).coord j (eichlerPeriod n F
          (binaryComplexReflection (basePoint A)) (h * atInfinity UpperHalfPlane.J)) *
            eichlerReflectedFunctional functional (binaryWeightBasis (n + 1) j)) := by
    intro A
    rw [eichler_functional_eichlerNormalTw, eichler_functional_eq_sum_coord functional,
      eichler_functional_eq_sum_coord (eichlerReflectedFunctional functional)]
  unfold Smooth
  refine ContDiffOn.congr (f := fun point : Fin 1 → Matrix (Fin 2) (Fin 2) ℝ => (2 : ℂ)⁻¹ *
      (∑ j, (binaryWeightBasis (n + 1)).coord j
          (eichlerPeriod n F (basePoint (invertibleMatrix (point 0))) h) *
          functional (binaryWeightBasis (n + 1) j) -
        ∑ j, (binaryWeightBasis (n + 1)).coord j (eichlerPeriod n F
          (binaryComplexReflection (basePoint (invertibleMatrix (point 0))))
            (h * atInfinity UpperHalfPlane.J)) *
            eichlerReflectedFunctional functional (binaryWeightBasis (n + 1) j))) ?_
    (fun point _ => expansion _)
  exact contDiffOn_const.mul (ContDiffOn.sub
    (ContDiffOn.sum fun j _ => (direct h j).mul contDiffOn_const)
    (ContDiffOn.sum fun j _ => (mirrored (h * atInfinity UpperHalfPlane.J) j).mul contDiffOn_const))

end Scalar

section Regular

variable {σ : CuspidalRepresentation} {n : ℕ} (D : EichlerInput σ n)

/-- The scalar twisted Eichler cocycle is the pointwise twisted Eichler normal form. -/
theorem eichlerCocycleTw_eq_eichlerNormalTw (stages : AnalyticScalar.ContinuousStages σ)
    (A : BinaryRealGL) :
    eichlerCocycleTw D A = eichlerNormalTw n (endpointScalar σ D.halfWeight D.vector) A := by
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
  unfold eichlerCocycleTw cocycleTw potentialTw
  rw [hilbertLift_smul σ _ _ diff_smooth, hilbertLift_sub σ _ _ first_smooth third_smooth,
    hilbertLift_binaryHilbertOperator σ UpperHalfPlane.J _ second_smooth,
    hilbertLift_binaryEndpointPeriod σ stages D.halfWeight D.vector D.fixedLevel _ positive,
    hilbertLift_binaryEndpointPeriod σ stages D.halfWeight D.vector D.fixedLevel _
      reflected_positive]
  rfl

/-- **Scalar analyticity.** Every coefficient of the twisted Eichler cocycle is a real-analytic
function of the real group element, at each fixed adelic point. -/
theorem eichlerCocycleTw_scalar_smooth (stages : AnalyticScalar.ContinuousStages σ)
    (m : Fin 2 →₀ ℕ) (A : BinaryAdelicGL) :
    Smooth (fun x : Fin 1 → BinaryRealGL => (eichlerCocycleTw D (x 0) A).val.coeff m) := by
  have holomorphic : ∀ h, DifferentiableOn ℂ (endpointScalar σ D.halfWeight D.vector h)
      {z : ℂ | 0 < z.im} := fun h =>
    cuspScalarWeightedRealization_holomorphic σ D.halfWeight D.vector D.vector_spherical
      D.rotation D.holomorphic h
  have regular := eichlerNormalTw_functional_smooth (n := n)
    (endpointScalar σ D.halfWeight D.vector) holomorphic A (coeffFunctional (n := n) m)
  unfold Smooth at regular ⊢
  refine regular.congr (fun point _ => ?_)
  exact congrArg (fun p : Binary.HomogeneousPoly (n + 1) => p.val.coeff m)
    (congrFun (eichlerCocycleTw_eq_eichlerNormalTw D stages (invertibleMatrix (point 0))) A)

/-- The Hilbert-level twisted cocycle is real analytic in the group element. -/
theorem cocycleTw_smoothFamily :
    Smooth (fun point : Fin 1 → BinaryRealGL => cocycleTw D (point 0)) := by
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
def liftVectorTw (stages : AnalyticScalar.ContinuousStages σ) (m : Fin 2 →₀ ℕ)
    (g : BinaryRealGL) : σ.smooth :=
  ∑ position, ((binaryWeightBasis (n + 1) position).val.coeff m) •
    (⟨cocycleTw D g position, cocycleTw_smooth D stages g position⟩ : σ.smooth)

theorem liftVectorTw_realize (stages : AnalyticScalar.ContinuousStages σ) (m : Fin 2 →₀ ℕ)
    (g : BinaryRealGL) (A : BinaryAdelicGL) :
    σ.realize (liftVectorTw D stages m g) A = (eichlerCocycleTw D g A).val.coeff m := by
  unfold liftVectorTw eichlerCocycleTw hilbertLift
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Submodule.coe_sum,
    Submodule.coe_smul, MvPolynomial.coeff_sum, MvPolynomial.coeff_smul]
  refine Finset.sum_congr rfl fun position _ => ?_
  rw [smoothRealize_of_mem σ ⟨_, cocycleTw_smooth D stages g position⟩, mul_comm]

theorem liftVectorTw_smooth (stages : AnalyticScalar.ContinuousStages σ) (m : Fin 2 →₀ ℕ) :
    Smooth (fun x : Fin 1 → BinaryRealGL => (liftVectorTw D stages m (x 0)).val) := by
  have normal := cocycleTw_smoothFamily D
  unfold Smooth at normal ⊢
  have components : ∀ position, ContDiffOn ℝ ⊤
      (fun point : Fin 1 → Matrix (Fin 2) (Fin 2) ℝ =>
        cocycleTw D (invertibleMatrix (point 0)) position)
      {point | ∀ position, (point position).det ≠ 0} := fun position =>
    contDiffOn_pi.mp normal position
  refine ContDiffOn.congr (f := fun point : Fin 1 → Matrix (Fin 2) (Fin 2) ℝ =>
    ∑ position, ((binaryWeightBasis (n + 1) position).val.coeff m) •
      cocycleTw D (invertibleMatrix (point 0)) position) ?_
    (fun point _ => ?_)
  · exact ContDiffOn.sum fun position _ => (components position).const_smul _
  · unfold liftVectorTw
    simp only [Submodule.coe_sum, Submodule.coe_smul]

theorem liftVectorTw_spherical (stages : AnalyticScalar.ContinuousStages σ) (m : Fin 2 →₀ ℕ)
    (g : BinaryRealGL) : (liftVectorTw D stages m g).val ∈ cuspSphericalValues σ := by
  unfold liftVectorTw
  rw [Submodule.coe_sum]
  refine Submodule.sum_mem _ fun position _ => ?_
  rw [Submodule.coe_smul]
  exact Submodule.smul_mem _ _
    ((mem_spherical_iff σ _).mpr fun k => cocycleTw_fixed D k g position)

theorem eichlerCocycleTw_binaryValues (stages : AnalyticScalar.ContinuousStages σ)
    (g : BinaryRealGL) : BinaryValues σ n (eichlerCocycleTw D g) := by
  intro m
  refine ⟨liftVectorTw D stages m g, ?_⟩
  funext A
  exact liftVectorTw_realize D stages m g A

end Regular

/-- The properties of a twisted Eichler cocycle `α`: the cocycle identity with the sign of the
determinant, the vanishing on orthogonal matrices, cuspidal values with explicit smooth spherical
lifts, scalar real-analyticity, and right `GL₂(Ẑ)`-invariance. -/
def IsEichlerCocycleTw (σ : CuspidalRepresentation) (n : ℕ)
    (α : BinaryRealGL → BinaryAdelicGL → Binary.HomogeneousPoly (n + 1)) : Prop :=
  (∀ g h x, α (g * h) x = α g x + signDet g • binaryCohomologicalAction n g (α h) x) ∧
  (∀ k : BinaryRealGL, k.val.transpose * k.val = 1 → ∀ x, α k x = 0) ∧
  (∀ g, BinaryValues σ n (α g)) ∧
  (∀ m : Fin 2 →₀ ℕ, ∃ v : BinaryRealGL → σ.smooth,
    Smooth (fun x : Fin 1 → BinaryRealGL => (v (x 0)).val) ∧
    (∀ g A, σ.realize (v g) A = (α g A).val.coeff m) ∧
    (∀ g, (v g).val ∈ cuspSphericalValues σ)) ∧
  (∀ (A : BinaryAdelicGL) (m : Fin 2 →₀ ℕ),
    Smooth (fun x : Fin 1 → BinaryRealGL => (α (x 0) A).val.coeff m)) ∧
  (∀ (k : GeneralLinearGroup (Fin 2) IntegralAdeles) (g : BinaryRealGL) (x : BinaryAdelicGL),
    α g (x * atFinite (GeneralLinearGroup.map integralEmbedding k)) = α g x)

/-- **The twisted Eichler cocycle exists** for every Eichler input. -/
theorem exists_eichlerCocycleTw {σ : CuspidalRepresentation} {n : ℕ}
    (stages : AnalyticScalar.ContinuousStages σ) (D : EichlerInput σ n) :
    ∃ α : BinaryRealGL → BinaryAdelicGL → Binary.HomogeneousPoly (n + 1),
      IsEichlerCocycleTw σ n α :=
  ⟨eichlerCocycleTw D,
    eichlerCocycleTw_mul D stages, eichlerCocycleTw_orthogonal D,
    eichlerCocycleTw_binaryValues D stages,
    fun m => ⟨liftVectorTw D stages m, liftVectorTw_smooth D stages m,
      liftVectorTw_realize D stages m, liftVectorTw_spherical D stages m⟩,
    fun A m => eichlerCocycleTw_scalar_smooth D stages m A,
    eichlerCocycleTw_finiteLevel D stages⟩

/-- **The twisted Eichler cocycle exists** for every spherical cuspidal representation with a
nonzero cohomology class of odd degree. -/
theorem exists_eichlerCocycleTw_of_cohomological (σ : CuspidalRepresentation)
    (spherical : SphericalCusp σ) {n : ℕ} (odd : Odd n) (cohomological : Cohomological σ n)
    (stages : AnalyticScalar.ContinuousStages σ) :
    ∃ α : BinaryRealGL → BinaryAdelicGL → Binary.HomogeneousPoly (n + 1),
      IsEichlerCocycleTw σ n α := by
  obtain ⟨D⟩ := EichlerInput.nonempty_of_cohomological σ spherical odd cohomological
  exact exists_eichlerCocycleTw stages D

end TernaryPeriodPolynomials.TwistedSource

end
