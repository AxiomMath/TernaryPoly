module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Source.LevelThreeEichlerPrimitive
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Source.GoodPlaneSourceData
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Eichler.Cocycle

@[expose] public section


/-!
# The level-three Eichler cocycle: scalar realization and packaging

Level-three version of SC's `EichlerLift`, `EichlerRegular`.  The Hilbert-level cocycle
`A ↦ P(A · i)` of a smooth holomorphic weight `-(n + 3)` vector fixed by the level-three Levi
level has smooth components fixed by that level.  Its realization `lteA` is a polynomial-valued
function on the adelic group satisfying the cocycle identity, vanishing on the orthogonal
group, with explicit smooth lifts in `levelThreeValues` and real-analytic scalar coefficients.
The result is packaged as `GoodPlaneSourceData.LevelLeviCocycleData` (`lteData`).

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.LevelThreeSource

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.AnalyticClasses
open TernaryPeriodPolynomials.PlaneEisensteinContinuation
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.Separation (PlaneLeviLevel)
open TernaryPeriodPolynomials.MultiplicityOne
  (LevelThreeCusp levelThreeValues mem_levelThreeValues)
open scoped Matrix.Norms.Elementwise

/-- The scalar-valued Eichler cocycle of a vector: the realization of the Hilbert-level
cocycle. -/
def lteAlpha (σ : CuspidalRepresentation) (n : ℕ) (halfWeight : ℤ) (v : σ.H) (A : BinaryRealGL) :
    BinaryAdelicGL → Binary.HomogeneousPoly (n + 1) :=
  hilbertLift σ n (lteCocycle σ n halfWeight v A)

section Lift

variable {σ : CuspidalRepresentation} {n : ℕ} (D : L3Input σ n)

theorem lteCoc_smooth (stages : AnalyticScalar.ContinuousStages σ) (A : BinaryRealGL)
    (position : Fin (n + 2)) : lteCoc D A position ∈ σ.smooth := by
  have positive := basePoint_im_pos A
  have reflected_positive : 0 < (binaryComplexReflection (basePoint A)).im := by
    rw [binaryComplexReflection_im]
    exact positive
  have first_smooth := binaryEndpointPeriod_smooth (n := n) σ stages D.halfWeight D.vector
    D.fixedLevel (basePoint A) positive
  have second_smooth := binaryEndpointPeriod_smooth (n := n) σ stages D.halfWeight D.vector
    D.fixedLevel (binaryComplexReflection (basePoint A)) reflected_positive
  have third_smooth := binaryHilbertOperator_smooth σ UpperHalfPlane.J _ second_smooth
  unfold lteCoc ltePot ltePotential
  exact σ.smooth.smul_mem _ (σ.smooth.add_mem (first_smooth position) (third_smooth position))

theorem lteCoc_fixed (k : GeneralLinearGroup (Fin 2) IntegralAdeles) (hk : PlaneLeviLevel k)
    (A : BinaryRealGL) (position : Fin (n + 2)) :
    σ.π (atFinite (GeneralLinearGroup.map integralEmbedding k)) (lteCoc D A position) =
      lteCoc D A position := by
  have positive := basePoint_im_pos A
  have reflected_positive : 0 < (binaryComplexReflection (basePoint A)).im := by
    rw [binaryComplexReflection_im]
    exact positive
  have second := binaryHilbertOperator_preserves_finiteLevel σ (binaryWeightBasis (n + 1))
    UpperHalfPlane.J (GeneralLinearGroup.map integralEmbedding k)
    (binaryEndpointPeriod σ n D.halfWeight D.vector.val (binaryComplexReflection (basePoint A)))
    (D.period_fixed k hk _ reflected_positive) position
  have first := D.period_fixed k hk (basePoint A) positive position
  unfold lteCoc ltePot ltePotential
  simp only [Pi.smul_apply, Pi.add_apply]
  rw [map_smul, map_add, first, second]

/-- The scalar-valued Eichler cocycle of the input vector of `D`: the realization of the
Hilbert-level cocycle. -/
def lteA (A : BinaryRealGL) : BinaryAdelicGL → Binary.HomogeneousPoly (n + 1) :=
  hilbertLift σ n (lteCoc D A)

theorem lteA_eq (A : BinaryRealGL) :
    lteA D A = lteAlpha σ n D.halfWeight D.vector.val A := rfl

/-- **The cocycle identity for the scalar Eichler cocycle.** -/
theorem lteA_mul (stages : AnalyticScalar.ContinuousStages σ) (g h : BinaryRealGL)
    (x : BinaryAdelicGL) :
    lteA D (g * h) x = lteA D g x + binaryCohomologicalAction n g (lteA D h) x := by
  have smooth_g := lteCoc_smooth D stages g
  have smooth_h := lteCoc_smooth D stages h
  have transported := binaryHilbertOperator_smooth σ g (lteCoc D h) smooth_h
  unfold lteA
  rw [lteCoc_mul, hilbertLift_add σ _ _ smooth_g transported,
    hilbertLift_binaryHilbertOperator σ g _ smooth_h]
  rfl

theorem lteA_eq_zero_of_smul_I (A : BinaryRealGL)
    (h : A • UpperHalfPlane.I = UpperHalfPlane.I) (x : BinaryAdelicGL) :
    lteA D A x = 0 := by
  unfold lteA
  rw [lteCoc_eq_zero_of_smul_I D A h]
  exact congrFun (EichlerInput.hilbertLift_zero' (σ := σ) (n := n)) x

/-- **The scalar Eichler cocycle vanishes on every orthogonal matrix.** -/
theorem lteA_orthogonal (k : BinaryRealGL) (hk : k.val.transpose * k.val = 1)
    (x : BinaryAdelicGL) : lteA D k x = 0 :=
  lteA_eq_zero_of_smul_I D k (orthogonal_smul_I k hk) x

/-- **Finite level**: the scalar Eichler cocycle is right invariant under the level-three Levi
level. -/
theorem lteA_finiteLevel (stages : AnalyticScalar.ContinuousStages σ)
    (k : GeneralLinearGroup (Fin 2) IntegralAdeles) (hk : PlaneLeviLevel k) (g : BinaryRealGL)
    (x : BinaryAdelicGL) :
    lteA D g (x * atFinite (GeneralLinearGroup.map integralEmbedding k)) = lteA D g x := by
  have step : ∀ position : Fin (n + 2),
      smoothRealize σ (lteCoc D g position)
        (x * atFinite (GeneralLinearGroup.map integralEmbedding k)) =
      smoothRealize σ (lteCoc D g position) x := by
    intro position
    rw [smoothRealize_of_mem σ ⟨_, lteCoc_smooth D stages g position⟩]
    have equivariant := σ.equivariant (atFinite (GeneralLinearGroup.map integralEmbedding k))
      ⟨lteCoc D g position, lteCoc_smooth D stages g position⟩ x
    have same : (⟨σ.π (atFinite (GeneralLinearGroup.map integralEmbedding k))
        (lteCoc D g position), σ.smooth_stable _ _ (lteCoc_smooth D stages g position)⟩ :
          σ.smooth) = ⟨lteCoc D g position, lteCoc_smooth D stages g position⟩ :=
      Subtype.ext (lteCoc_fixed D k hk g position)
    rw [← equivariant]
    exact congrArg (fun v : σ.smooth => σ.realize v x) same
  unfold lteA hilbertLift
  exact Finset.sum_congr rfl fun position _ => by rw [step position]

/-- The scalar Eichler cocycle is the pointwise Eichler normal form. -/
theorem lteA_eq_eichlerNormal (stages : AnalyticScalar.ContinuousStages σ) (A : BinaryRealGL) :
    lteA D A = eichlerNormal n (endpointScalar σ D.halfWeight D.vector) A := by
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
  unfold lteA lteCoc ltePot ltePotential
  rw [hilbertLift_smul σ _ _ sum_smooth, hilbertLift_add σ _ _ first_smooth third_smooth,
    hilbertLift_binaryHilbertOperator σ UpperHalfPlane.J _ second_smooth,
    hilbertLift_binaryEndpointPeriod σ stages D.halfWeight D.vector D.fixedLevel _ positive,
    hilbertLift_binaryEndpointPeriod σ stages D.halfWeight D.vector D.fixedLevel _
      reflected_positive]
  rfl

/-- **Scalar analyticity.** Every coefficient of the Eichler cocycle is a real-analytic function
of the real group element, at each fixed adelic point. -/
theorem lteA_scalar_smooth (stages : AnalyticScalar.ContinuousStages σ)
    (m : Fin 2 →₀ ℕ) (A : BinaryAdelicGL) :
    Smooth (fun x : Fin 1 → BinaryRealGL => (lteA D (x 0) A).val.coeff m) := by
  have holomorphic : ∀ h, DifferentiableOn ℂ (endpointScalar σ D.halfWeight D.vector h)
      {z : ℂ | 0 < z.im} := fun h =>
    MultiplicityOne.cuspScalarWeightedRealization_holomorphic σ D.halfWeight D.vector
      D.vector_level D.rotation D.holomorphic h
  have regular := eichlerNormal_functional_smooth (n := n)
    (endpointScalar σ D.halfWeight D.vector) holomorphic A (coeffFunctional (n := n) m)
  unfold Smooth at regular ⊢
  refine regular.congr (fun point _ => ?_)
  exact congrArg (fun p : Binary.HomogeneousPoly (n + 1) => p.val.coeff m)
    (congrFun (lteA_eq_eichlerNormal D stages (invertibleMatrix (point 0))) A)

/-- The Hilbert-level cocycle is real analytic in the group element. -/
theorem lteCoc_smoothFamily :
    Smooth (fun point : Fin 1 → BinaryRealGL => lteCoc D (point 0)) := by
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
  exact (first.add third).const_smul (2 : ℂ)⁻¹

/-- The smooth lift of a monomial coefficient of the Eichler cocycle. -/
def lteLift (stages : AnalyticScalar.ContinuousStages σ) (m : Fin 2 →₀ ℕ)
    (g : BinaryRealGL) : σ.smooth :=
  ∑ position, ((binaryWeightBasis (n + 1) position).val.coeff m) •
    (⟨lteCoc D g position, lteCoc_smooth D stages g position⟩ : σ.smooth)

theorem lteLift_realize (stages : AnalyticScalar.ContinuousStages σ) (m : Fin 2 →₀ ℕ)
    (g : BinaryRealGL) (A : BinaryAdelicGL) :
    σ.realize (lteLift D stages m g) A = (lteA D g A).val.coeff m := by
  unfold lteLift lteA hilbertLift
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Submodule.coe_sum,
    Submodule.coe_smul, MvPolynomial.coeff_sum, MvPolynomial.coeff_smul]
  refine Finset.sum_congr rfl fun position _ => ?_
  rw [smoothRealize_of_mem σ ⟨_, lteCoc_smooth D stages g position⟩, mul_comm]

theorem lteLift_smooth (stages : AnalyticScalar.ContinuousStages σ) (m : Fin 2 →₀ ℕ) :
    Smooth (fun x : Fin 1 → BinaryRealGL => (lteLift D stages m (x 0)).val) := by
  have normal := lteCoc_smoothFamily D
  unfold Smooth at normal ⊢
  have components : ∀ position, ContDiffOn ℝ ⊤
      (fun point : Fin 1 → Matrix (Fin 2) (Fin 2) ℝ =>
        lteCoc D (invertibleMatrix (point 0)) position)
      {point | ∀ position, (point position).det ≠ 0} := fun position =>
    contDiffOn_pi.mp normal position
  refine ContDiffOn.congr (f := fun point : Fin 1 → Matrix (Fin 2) (Fin 2) ℝ =>
    ∑ position, ((binaryWeightBasis (n + 1) position).val.coeff m) •
      lteCoc D (invertibleMatrix (point 0)) position) ?_
    (fun point _ => ?_)
  · exact ContDiffOn.sum fun position _ => (components position).const_smul _
  · unfold lteLift
    simp only [Submodule.coe_sum, Submodule.coe_smul]

theorem lteLift_level (stages : AnalyticScalar.ContinuousStages σ) (m : Fin 2 →₀ ℕ)
    (g : BinaryRealGL) : (lteLift D stages m g).val ∈ levelThreeValues σ := by
  unfold lteLift
  rw [Submodule.coe_sum]
  refine Submodule.sum_mem _ fun position _ => ?_
  rw [Submodule.coe_smul]
  exact Submodule.smul_mem _ _
    (mem_levelThreeValues.mpr fun k hk => lteCoc_fixed D k hk g position)

/-- **The level-three Levi cocycle datum of an Eichler input**: the Eichler cocycle
`A ↦ ½ (Per(A i) + J Per(-conj(A i)))` with its regularity package. -/
def lteData (stages : AnalyticScalar.ContinuousStages σ) : LevelLeviCocycleData σ n where
  α := lteA D
  cocycle := fun g h x => lteA_mul D stages g h x
  orth := fun k hk x => lteA_orthogonal D k hk x
  lift := lteLift D stages
  lift_realize := fun μ g A => lteLift_realize D stages μ g A
  lift_smooth := fun μ => lteLift_smooth D stages μ
  scalar_smooth := fun μ A => lteA_scalar_smooth D stages μ A
  level := fun μ g => lteLift_level D stages μ g

theorem lteData_α (stages : AnalyticScalar.ContinuousStages σ) :
    (lteData D stages).α = lteA D := rfl

end Lift

end TernaryPeriodPolynomials.LevelThreeSource

end
