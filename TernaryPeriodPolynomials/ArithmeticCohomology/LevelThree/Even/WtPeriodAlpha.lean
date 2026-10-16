module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.L3PeriodPrimitive
public import TernaryPeriodPolynomials.ArithmeticCohomology.MultiplicityOne.DictionaryInjective
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Even.WtScalarHolomorphic
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Even.WtL3TwLiftB

@[expose] public section


/-!
# The weight-generic level-three Eichler cocycle at the identity is the classical period cocycle

Formalized by Claude Sonnet 5.5 (AxiomCode).

Twins of `L3PeriodAlpha` for an integer rotation weight `wt = -(n + 3)` (odd or even `n`).  For an
Eichler input `I : L3InputWt σ n` whose scalar weighted realization is the function `f` on the upper
half plane, the sign-twisted Eichler cocycle evaluated at the identity adele is

`α A 1 = ½ (P (A i) - J_* P (-conj (A i)))`,   `P = LevelThreePeriodPrimitive.primitive (n + 1) f`.

* `l3p_scalar_JWt`: the scalar realization is invariant under the reflection `J`;
* `l3p_scalar_one_eqWt`: the scalar realization at the identity is `f` on the upper half plane;
* `l3p_alpha_one_eq_formulaWt`: the formula above.
-/

noncomputable section

namespace TernaryPeriodPolynomials.EvenLevelThree

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Manifold
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.AnalyticClasses
open TernaryPeriodPolynomials.PlaneEisensteinContinuation
open TernaryPeriodPolynomials.TwistedSource
open TernaryPeriodPolynomials.LevelThree
open TernaryPeriodPolynomials.SourceConstruction (l3p_eichlerPeriod_eq_primitive)

/-- The scalar weighted realization of a level-three vector is invariant under the real reflection
`J` on the right of the base point. -/
theorem l3p_scalar_JWt (σ : CuspidalRepresentation) (wt : ℤ) (v : σ.smooth)
    (hv : v.val ∈ MultiplicityOne.levelThreeValues σ) (w : ℂ) :
    cuspScalarWeightedRealizationWt σ wt v (1 * atInfinity UpperHalfPlane.J) w =
      cuspScalarWeightedRealizationWt σ wt v 1 w := by
  unfold cuspScalarWeightedRealizationWt cuspScalarAffineRealization
  simp only [one_mul]
  rw [← atInfinity_mul, MultiplicityOne.levelThree_realization_reflection σ v hv]

/-- On the upper half plane the scalar weighted realization at the identity is the function `f`. -/
theorem l3p_scalar_one_eqWt {σ : CuspidalRepresentation} {wt : ℤ} {v : σ.smooth}
    {f : UpperHalfPlane → ℂ} (hf : f = cuspScalarWeightedLinearWt σ wt 1 v) {w : ℂ}
    (hz : 0 < w.im) :
    cuspScalarWeightedRealizationWt σ wt v 1 w = f (UpperHalfPlane.ofComplex w) := by
  have value := congrFun hf (UpperHalfPlane.ofComplex w)
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz] at value
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz]
  exact value.symm

/-- **The weight-generic level-three sign-twisted Eichler cocycle at the identity adele in terms of
the classical primitive.** -/
theorem l3p_alpha_one_eq_formulaWt {σ : CuspidalRepresentation} {n : ℕ} (I : L3InputWt σ n)
    (stages : AnalyticScalar.ContinuousStages σ) {f : UpperHalfPlane → ℂ}
    (hf : f = cuspScalarWeightedLinearWt σ I.wt 1 I.vector)
    (hfd : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (A : BinaryRealGL) :
    I.alpha A 1 = (2 : ℂ)⁻¹ • (LevelThreePeriodPrimitive.primitive (n + 1) f (basePoint A) -
      binaryCoefficient n UpperHalfPlane.J
        (LevelThreePeriodPrimitive.primitive (n + 1) f
          (binaryComplexReflection (basePoint A)))) := by
  have unimodular : |(UpperHalfPlane.J : BinaryRealGL).val.det| = 1 := by
    rw [det_upperJ]
    norm_num
  have positive := basePoint_im_pos A
  have reflected_positive : 0 < (binaryComplexReflection (basePoint A)).im := by
    rw [binaryComplexReflection_im]
    exact positive
  have holomorphic : ∀ h, DifferentiableOn ℂ (endpointScalarWt σ I.wt I.vector h)
      {z : ℂ | 0 < z.im} := fun h =>
    cuspScalarWeightedRealization_holomorphicWt σ stages I.wt I.vector
      I.fixedLevel I.holomorphic h
  have first : eichlerPeriod n (endpointScalarWt σ I.wt I.vector) (basePoint A) 1 =
      LevelThreePeriodPrimitive.primitive (n + 1) f (basePoint A) :=
    l3p_eichlerPeriod_eq_primitive n hfd (endpointScalarWt σ I.wt I.vector) holomorphic 1
      (fun w hz => l3p_scalar_one_eqWt hf hz) positive
  have second : eichlerPeriod n (endpointScalarWt σ I.wt I.vector)
      (binaryComplexReflection (basePoint A)) (1 * atInfinity UpperHalfPlane.J) =
        LevelThreePeriodPrimitive.primitive (n + 1) f (binaryComplexReflection (basePoint A)) :=
    l3p_eichlerPeriod_eq_primitive n hfd (endpointScalarWt σ I.wt I.vector) holomorphic
      (1 * atInfinity UpperHalfPlane.J)
      (fun w hz => (l3p_scalar_JWt σ I.wt I.vector I.vector_level w).trans
        (l3p_scalar_one_eqWt hf hz)) reflected_positive
  rw [congrFun (I.alpha_eq_eichlerNormalTw stages A) 1]
  unfold eichlerNormalTw
  rw [binaryAmbientRepresentation_apply_of_unimodular unimodular, first, second]

end TernaryPeriodPolynomials.EvenLevelThree

end
