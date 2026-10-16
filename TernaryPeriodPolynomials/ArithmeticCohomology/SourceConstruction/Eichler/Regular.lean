module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Eichler.Lift
public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Eichler.Regularity

@[expose] public section


/-!
# Regularity of the scalar Eichler cocycle and its packaging

The Eichler cocycle of a holomorphic lowest-weight vector has explicit smooth lifts into the
smooth vectors of the cuspidal representation, real-analytic scalar coefficients, and is
bi-invariant for the finite level. These are the ingredients of `GeneralEisenstein.Cohomological`
together with the real-analyticity that the abstract cocycle lacks.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.SourceConstruction

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.AnalyticClasses
open TernaryPeriodPolynomials.PlaneEisensteinContinuation
open scoped Matrix.Norms.Elementwise

section Scalar

variable {n : ℕ}

/-- The functional picking out the coefficient of a monomial. -/
def coeffFunctional (m : Fin 2 →₀ ℕ) : Binary.HomogeneousPoly (n + 1) →ₗ[ℂ] ℂ where
  toFun p := p.val.coeff m
  map_add' p q := by simp
  map_smul' c p := by simp

theorem coeffFunctional_apply (m : Fin 2 →₀ ℕ) (p : Binary.HomogeneousPoly (n + 1)) :
    coeffFunctional m p = p.val.coeff m := rfl

theorem eichler_functional_eq_sum_coord (functional : Binary.HomogeneousPoly (n + 1) →ₗ[ℂ] ℂ)
    (polynomial : Binary.HomogeneousPoly (n + 1)) :
    functional polynomial = ∑ position, (binaryWeightBasis (n + 1)).coord position polynomial *
      functional (binaryWeightBasis (n + 1) position) := by
  calc functional polynomial = functional (∑ position,
      (binaryWeightBasis (n + 1)).coord position polynomial •
        binaryWeightBasis (n + 1) position) := by
        simp only [Module.Basis.coord_apply, Module.Basis.sum_repr]
    _ = _ := by
        rw [map_sum]
        exact Finset.sum_congr rfl fun position _ => by rw [map_smul, smul_eq_mul]

/-- The reflection action on coefficients, followed by a functional. -/
def eichlerReflectedFunctional (functional : Binary.HomogeneousPoly (n + 1) →ₗ[ℂ] ℂ) :
    Binary.HomogeneousPoly (n + 1) →ₗ[ℂ] ℂ :=
  functional.comp (normPower (Matrix.GeneralLinearGroup.det (atInfinity UpperHalfPlane.J))
    (((n : ℂ) + 3) / 2) • binaryCoefficient n UpperHalfPlane.J)

theorem eichler_functional_eichlerNormal (F : BinaryAdelicGL → ℂ → ℂ)
    (functional : Binary.HomogeneousPoly (n + 1) →ₗ[ℂ] ℂ) (A : BinaryRealGL)
    (h : BinaryAdelicGL) :
    functional (eichlerNormal n F A h) = (2 : ℂ)⁻¹ *
      (functional (eichlerPeriod n F (basePoint A) h) +
        eichlerReflectedFunctional functional (eichlerPeriod n F
          (binaryComplexReflection (basePoint A)) (h * atInfinity UpperHalfPlane.J))) := by
  rw [eichlerNormal_def, map_smul, map_add, smul_eq_mul]
  rfl

/-- Each coordinate of the scalar Eichler period is real analytic in its endpoint. -/
theorem coordPeriod_contDiffOn (F : BinaryAdelicGL → ℂ → ℂ)
    (holomorphic : ∀ h, DifferentiableOn ℂ (F h) {z : ℂ | 0 < z.im}) (h : BinaryAdelicGL)
    (j : Fin (n + 2)) :
    ContDiffOn ℝ ⊤ (fun w : ℂ => (binaryWeightBasis (n + 1)).coord j (eichlerPeriod n F w h))
      {w : ℂ | 0 < w.im} := by
  have differentiable : DifferentiableOn ℂ
      (fun w : ℂ => (binaryWeightBasis (n + 1)).coord j (eichlerPeriod n F w h))
      {w : ℂ | 0 < w.im} := fun w hw =>
    (hasDerivAt_coord_eichlerPeriod F holomorphic hw h j).differentiableAt.differentiableWithinAt
  exact fun w hw => ((differentiable.analyticAt (eichlerUpperSet_isOpen.mem_nhds hw)).restrictScalars
    (𝕜 := ℝ)).contDiffAt.contDiffWithinAt

/-- **Real analyticity of the functionals of the pointwise Eichler normal form.** -/
theorem eichlerNormal_functional_smooth (F : BinaryAdelicGL → ℂ → ℂ)
    (holomorphic : ∀ h, DifferentiableOn ℂ (F h) {z : ℂ | 0 < z.im}) (h : BinaryAdelicGL)
    (functional : Binary.HomogeneousPoly (n + 1) →ₗ[ℂ] ℂ) :
    Smooth (fun x : Fin 1 → BinaryRealGL => functional (eichlerNormal n F (x 0) h)) := by
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
  have expansion : ∀ A : BinaryRealGL, functional (eichlerNormal n F A h) = (2 : ℂ)⁻¹ *
      (∑ j, (binaryWeightBasis (n + 1)).coord j (eichlerPeriod n F (basePoint A) h) *
          functional (binaryWeightBasis (n + 1) j) +
        ∑ j, (binaryWeightBasis (n + 1)).coord j (eichlerPeriod n F
          (binaryComplexReflection (basePoint A)) (h * atInfinity UpperHalfPlane.J)) *
            eichlerReflectedFunctional functional (binaryWeightBasis (n + 1) j)) := by
    intro A
    rw [eichler_functional_eichlerNormal, eichler_functional_eq_sum_coord functional,
      eichler_functional_eq_sum_coord (eichlerReflectedFunctional functional)]
  unfold Smooth
  refine ContDiffOn.congr (f := fun point : Fin 1 → Matrix (Fin 2) (Fin 2) ℝ => (2 : ℂ)⁻¹ *
      (∑ j, (binaryWeightBasis (n + 1)).coord j
          (eichlerPeriod n F (basePoint (invertibleMatrix (point 0))) h) *
          functional (binaryWeightBasis (n + 1) j) +
        ∑ j, (binaryWeightBasis (n + 1)).coord j (eichlerPeriod n F
          (binaryComplexReflection (basePoint (invertibleMatrix (point 0))))
            (h * atInfinity UpperHalfPlane.J)) *
            eichlerReflectedFunctional functional (binaryWeightBasis (n + 1) j))) ?_
    (fun point _ => expansion _)
  exact contDiffOn_const.mul (ContDiffOn.add
    (ContDiffOn.sum fun j _ => (direct h j).mul contDiffOn_const)
    (ContDiffOn.sum fun j _ => (mirrored (h * atInfinity UpperHalfPlane.J) j).mul contDiffOn_const))

end Scalar

namespace EichlerInput

variable {σ : CuspidalRepresentation} {n : ℕ} (D : EichlerInput σ n)

/-- The scalar Eichler cocycle is the pointwise Eichler normal form. -/
theorem eichlerCocycle_eq_eichlerNormal (stages : AnalyticScalar.ContinuousStages σ)
    (A : BinaryRealGL) :
    D.eichlerCocycle A = eichlerNormal n (endpointScalar σ D.halfWeight D.vector) A := by
  have positive := basePoint_im_pos A
  have reflected_positive : 0 < (binaryComplexReflection (basePoint A)).im := by
    rw [binaryComplexReflection_im]
    exact positive
  have first_smooth := binaryEndpointPeriod_smooth (n := n) σ stages D.halfWeight D.vector
    D.fixedLevel (basePoint A) positive
  have second_smooth := binaryEndpointPeriod_smooth (n := n) σ stages D.halfWeight D.vector
    D.fixedLevel (binaryComplexReflection (basePoint A)) reflected_positive
  have third_smooth := binaryHilbertOperator_smooth σ UpperHalfPlane.J _ second_smooth
  have sum_smooth : ∀ position, (binaryEndpointPeriod σ n D.halfWeight D.vector.val (basePoint A) +
      binaryHilbertOperator σ (binaryWeightBasis (n + 1)) UpperHalfPlane.J
        (binaryEndpointPeriod σ n D.halfWeight D.vector.val
          (binaryComplexReflection (basePoint A)))) position ∈ σ.smooth :=
    fun position => σ.smooth.add_mem (first_smooth position) (third_smooth position)
  unfold eichlerCocycle cocycle potential
  rw [hilbertLift_smul σ _ _ sum_smooth, hilbertLift_add σ _ _ first_smooth third_smooth,
    hilbertLift_binaryHilbertOperator σ UpperHalfPlane.J _ second_smooth,
    hilbertLift_binaryEndpointPeriod σ stages D.halfWeight D.vector D.fixedLevel _ positive,
    hilbertLift_binaryEndpointPeriod σ stages D.halfWeight D.vector D.fixedLevel _
      reflected_positive]
  rfl

/-- **Scalar analyticity.** Every coefficient of the Eichler cocycle is a real-analytic function
of the real group element, at each fixed adelic point. -/
theorem eichlerCocycle_scalar_smooth (stages : AnalyticScalar.ContinuousStages σ)
    (m : Fin 2 →₀ ℕ) (A : BinaryAdelicGL) :
    Smooth (fun x : Fin 1 → BinaryRealGL => (D.eichlerCocycle (x 0) A).val.coeff m) := by
  have holomorphic : ∀ h, DifferentiableOn ℂ (endpointScalar σ D.halfWeight D.vector h)
      {z : ℂ | 0 < z.im} := fun h =>
    cuspScalarWeightedRealization_holomorphic σ D.halfWeight D.vector D.vector_spherical
      D.rotation D.holomorphic h
  have regular := eichlerNormal_functional_smooth (n := n)
    (endpointScalar σ D.halfWeight D.vector) holomorphic A (coeffFunctional (n := n) m)
  unfold Smooth at regular ⊢
  refine regular.congr (fun point _ => ?_)
  exact congrArg (fun p : Binary.HomogeneousPoly (n + 1) => p.val.coeff m)
    (congrFun (D.eichlerCocycle_eq_eichlerNormal stages (invertibleMatrix (point 0))) A)

/-- The smooth lift of a monomial coefficient of the Eichler cocycle. -/
def liftVector (stages : AnalyticScalar.ContinuousStages σ) (m : Fin 2 →₀ ℕ) (g : BinaryRealGL) :
    σ.smooth :=
  ∑ position, ((binaryWeightBasis (n + 1) position).val.coeff m) •
    (⟨D.cocycle g position, D.cocycle_smooth stages g position⟩ : σ.smooth)

theorem liftVector_realize (stages : AnalyticScalar.ContinuousStages σ) (m : Fin 2 →₀ ℕ)
    (g : BinaryRealGL) (A : BinaryAdelicGL) :
    σ.realize (D.liftVector stages m g) A = (D.eichlerCocycle g A).val.coeff m := by
  unfold liftVector eichlerCocycle hilbertLift
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Submodule.coe_sum,
    Submodule.coe_smul, MvPolynomial.coeff_sum, MvPolynomial.coeff_smul]
  refine Finset.sum_congr rfl fun position _ => ?_
  rw [smoothRealize_of_mem σ ⟨_, D.cocycle_smooth stages g position⟩, mul_comm]

theorem liftVector_smooth (stages : AnalyticScalar.ContinuousStages σ) (m : Fin 2 →₀ ℕ) :
    Smooth (fun x : Fin 1 → BinaryRealGL => (D.liftVector stages m (x 0)).val) := by
  have normal := hilbertNormal_smooth σ n D.halfWeight D.vector
  unfold Smooth at normal ⊢
  have components : ∀ position, ContDiffOn ℝ ⊤
      (fun point : Fin 1 → Matrix (Fin 2) (Fin 2) ℝ =>
        hilbertNormal σ n D.halfWeight D.vector.val (invertibleMatrix (point 0)) position)
      {point | ∀ position, (point position).det ≠ 0} := fun position =>
    contDiffOn_pi.mp normal position
  refine ContDiffOn.congr (f := fun point : Fin 1 → Matrix (Fin 2) (Fin 2) ℝ =>
    ∑ position, ((binaryWeightBasis (n + 1) position).val.coeff m) •
      hilbertNormal σ n D.halfWeight D.vector.val (invertibleMatrix (point 0)) position) ?_
    (fun point _ => ?_)
  · exact ContDiffOn.sum fun position _ => (components position).const_smul _
  · unfold liftVector
    simp only [Submodule.coe_sum, Submodule.coe_smul]
    rfl

theorem liftVector_spherical (stages : AnalyticScalar.ContinuousStages σ) (m : Fin 2 →₀ ℕ)
    (g : BinaryRealGL) : (D.liftVector stages m g).val ∈ cuspSphericalValues σ := by
  unfold liftVector
  rw [Submodule.coe_sum]
  refine Submodule.sum_mem _ fun position _ => ?_
  rw [Submodule.coe_smul]
  exact Submodule.smul_mem _ _
    ((mem_spherical_iff σ _).mpr fun k => D.cocycle_fixed k g position)

theorem eichlerCocycle_binaryValues (stages : AnalyticScalar.ContinuousStages σ)
    (g : BinaryRealGL) : BinaryValues σ n (D.eichlerCocycle g) := by
  intro m
  refine ⟨D.liftVector stages m g, ?_⟩
  funext A
  exact D.liftVector_realize stages m g A

/-- **The Eichler cocycle**, in the format of `GeneralEisenstein.Cohomological`, with the extra
regularity: smooth lifts, real-analytic scalar coefficients, finite level, and vanishing on the
orthogonal group. -/
theorem eichlerCocycle_spec (stages : AnalyticScalar.ContinuousStages σ) :
    (∀ g h x, D.eichlerCocycle (g * h) x =
      D.eichlerCocycle g x + binaryCohomologicalAction n g (D.eichlerCocycle h) x) ∧
    (∀ k : BinaryRealGL, k.val.transpose * k.val = 1 → ∀ x, D.eichlerCocycle k x = 0) ∧
    (∀ g, BinaryValues σ n (D.eichlerCocycle g)) ∧
    (∀ m : Fin 2 →₀ ℕ, ∃ v : BinaryRealGL → σ.smooth,
      Smooth (fun x : Fin 1 → BinaryRealGL => (v (x 0)).val) ∧
      (∀ g A, σ.realize (v g) A = (D.eichlerCocycle g A).val.coeff m) ∧
      (∀ g, (v g).val ∈ cuspSphericalValues σ)) ∧
    (∀ (A : BinaryAdelicGL) (m : Fin 2 →₀ ℕ),
      Smooth (fun x : Fin 1 → BinaryRealGL => (D.eichlerCocycle (x 0) A).val.coeff m)) ∧
    (∀ (k : GeneralLinearGroup (Fin 2) IntegralAdeles) (g : BinaryRealGL) (x : BinaryAdelicGL),
      D.eichlerCocycle g (x * atFinite (GeneralLinearGroup.map integralEmbedding k)) =
        D.eichlerCocycle g x) :=
  ⟨D.eichlerCocycle_mul stages, D.eichlerCocycle_orthogonal, D.eichlerCocycle_binaryValues stages,
    fun m => ⟨D.liftVector stages m, D.liftVector_smooth stages m, D.liftVector_realize stages m,
      D.liftVector_spherical stages m⟩,
    fun A m => D.eichlerCocycle_scalar_smooth stages m A, D.eichlerCocycle_finiteLevel stages⟩

/-- A spherical cuspidal representation with a nonzero cohomology class of odd degree supplies
the input of the Eichler construction. -/
theorem nonempty_of_cohomological (σ : CuspidalRepresentation) (spherical : SphericalCusp σ)
    {n : ℕ} (odd : Odd n) (cohomological : Cohomological σ n) : Nonempty (EichlerInput σ n) := by
  obtain ⟨halfWeight, vector, weight, nonzero, member, rotation, _, holomorphic⟩ :=
    cohomological_exists_spherical_holomorphic σ spherical odd cohomological
  exact ⟨{ central_positive := cohomological_centralCharacter_positive σ cohomological
           halfWeight := halfWeight
           weight := weight
           vector := vector
           vector_ne := nonzero
           vector_spherical := member
           rotation := rotation
           holomorphic := holomorphic }⟩

end EichlerInput

end TernaryPeriodPolynomials.SourceConstruction

end
