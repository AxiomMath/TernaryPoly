module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Even.WtL3TwLiftA
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Even.WtScalarHolomorphic

@[expose] public section


/-!
# The weight-generic level-three sign-twisted Eichler cocycle: packaging, second half

Formalized by Claude Sonnet 5.5 (AxiomCode).

Twins of the second half of `L3EichlerLift` for `L3InputWt`: the scalar twisted Eichler cocycle is
the pointwise twisted Eichler normal form of the weighted scalar realization of the input vector,
its coefficients are real analytic, and it carries smooth lifts fixed by the level-three Levi level.
The result is packaged as `LineLeviCocycleData3` whose cocycle is `l3AlphaWt σ n wt vector`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.EvenLevelThree

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.AnalyticClasses
open TernaryPeriodPolynomials.PlaneEisensteinContinuation
open TernaryPeriodPolynomials.TwistedSource
open TernaryPeriodPolynomials.MultiplicityOne (levelThreeValues mem_levelThreeValues)
open TernaryPeriodPolynomials.SourceConstruction
  (coeffFunctional LineLeviCocycleData3)
open scoped Matrix.Norms.Elementwise

namespace L3InputWt

variable {σ : CuspidalRepresentation} {n : ℕ} (D : L3InputWt σ n)

/-- The scalar twisted Eichler cocycle is the pointwise twisted Eichler normal form. -/
theorem alpha_eq_eichlerNormalTw (stages : AnalyticScalar.ContinuousStages σ)
    (A : BinaryRealGL) :
    D.alpha A = eichlerNormalTw n (endpointScalarWt σ D.wt D.vector) A := by
  have positive := basePoint_im_pos A
  have reflected_positive : 0 < (binaryComplexReflection (basePoint A)).im := by
    rw [binaryComplexReflection_im]
    exact positive
  have first_smooth := binaryEndpointPeriod_smoothWt (n := n) σ stages D.wt D.vector
    D.fixedLevel (basePoint A) positive
  have second_smooth := binaryEndpointPeriod_smoothWt (n := n) σ stages D.wt D.vector
    D.fixedLevel (binaryComplexReflection (basePoint A)) reflected_positive
  have third_smooth := binaryHilbertOperator_smooth σ UpperHalfPlane.J _ second_smooth
  have diff_smooth : ∀ position, (binaryEndpointPeriodWt σ n D.wt D.vector.val (basePoint A) -
      binaryHilbertOperator σ (binaryWeightBasis (n + 1)) UpperHalfPlane.J
        (binaryEndpointPeriodWt σ n D.wt D.vector.val
          (binaryComplexReflection (basePoint A)))) position ∈ σ.smooth :=
    fun position => σ.smooth.sub_mem (first_smooth position) (third_smooth position)
  unfold L3InputWt.alpha L3InputWt.cocycle L3InputWt.potential l3PotentialWt
  rw [hilbertLift_smul σ _ _ diff_smooth, hilbertLift_sub σ _ _ first_smooth third_smooth,
    hilbertLift_binaryHilbertOperator σ UpperHalfPlane.J _ second_smooth,
    hilbertLift_binaryEndpointPeriodWt σ stages D.wt D.vector D.fixedLevel _ positive,
    hilbertLift_binaryEndpointPeriodWt σ stages D.wt D.vector D.fixedLevel _
      reflected_positive]
  rfl

/-- **Scalar analyticity.** Every coefficient of the twisted Eichler cocycle is a real-analytic
function of the real group element, at each fixed adelic point. -/
theorem alpha_scalar_smooth (stages : AnalyticScalar.ContinuousStages σ)
    (m : Fin 2 →₀ ℕ) (A : BinaryAdelicGL) :
    Smooth (fun x : Fin 1 → BinaryRealGL => (D.alpha (x 0) A).val.coeff m) := by
  have holomorphic : ∀ h, DifferentiableOn ℂ (endpointScalarWt σ D.wt D.vector h)
      {z : ℂ | 0 < z.im} := fun h =>
    cuspScalarWeightedRealization_holomorphicWt σ stages D.wt D.vector D.fixedLevel
      D.holomorphic h
  have regular := eichlerNormalTw_functional_smooth (n := n)
    (endpointScalarWt σ D.wt D.vector) holomorphic A (coeffFunctional (n := n) m)
  unfold Smooth at regular ⊢
  refine regular.congr (fun point _ => ?_)
  exact congrArg (fun p : Binary.HomogeneousPoly (n + 1) => p.val.coeff m)
    (congrFun (D.alpha_eq_eichlerNormalTw stages (invertibleMatrix (point 0))) A)

/-- The Hilbert-level twisted cocycle is real analytic in the group element. -/
theorem cocycle_smoothFamily :
    Smooth (fun point : Fin 1 → BinaryRealGL => D.cocycle (point 0)) := by
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
  exact (first.sub third).const_smul (2 : ℂ)⁻¹

/-- The smooth lift of a monomial coefficient of the twisted Eichler cocycle. -/
def liftVector (stages : AnalyticScalar.ContinuousStages σ) (m : Fin 2 →₀ ℕ)
    (g : BinaryRealGL) : σ.smooth :=
  ∑ position, ((binaryWeightBasis (n + 1) position).val.coeff m) •
    (⟨D.cocycle g position, D.cocycle_smooth stages g position⟩ : σ.smooth)

theorem liftVector_realize (stages : AnalyticScalar.ContinuousStages σ) (m : Fin 2 →₀ ℕ)
    (g : BinaryRealGL) (A : BinaryAdelicGL) :
    σ.realize (D.liftVector stages m g) A = (D.alpha g A).val.coeff m := by
  unfold L3InputWt.liftVector L3InputWt.alpha hilbertLift
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
  · unfold L3InputWt.liftVector
    simp only [Submodule.coe_sum, Submodule.coe_smul]

theorem liftVector_level (stages : AnalyticScalar.ContinuousStages σ) (m : Fin 2 →₀ ℕ)
    (g : BinaryRealGL) : (D.liftVector stages m g).val ∈ levelThreeValues σ := by
  unfold L3InputWt.liftVector
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

/-- **The level-three line Levi cocycle datum of a weight-generic Eichler input**: the sign-twisted
Eichler cocycle `A ↦ ½ (Per(A i) - J Per(-conj(A i)))` with its regularity package. -/
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

/-- The cocycle of the packaged datum is the scalar twisted Eichler cocycle `l3AlphaWt` of the
input vector. -/
theorem toData_α_eq_l3AlphaWt (stages : AnalyticScalar.ContinuousStages σ) :
    (D.toData stages).α = l3AlphaWt σ n D.wt D.vector.val := rfl

end L3InputWt

end TernaryPeriodPolynomials.EvenLevelThree

end
