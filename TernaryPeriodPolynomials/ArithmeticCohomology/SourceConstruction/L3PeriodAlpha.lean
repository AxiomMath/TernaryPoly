module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.L3EichlerLift
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.L3PeriodPrimitive
public import TernaryPeriodPolynomials.ArithmeticCohomology.MultiplicityOne.DictionaryInjective

@[expose] public section


/-!
# The level-three Eichler cocycle at the identity is the classical period cocycle

For an Eichler input `I : L3Input σ n` (a smooth holomorphic weight `-(n + 3)` vector fixed by the
level-three Levi level) whose scalar weighted realization is the function `f` on the upper half plane,
the sign-twisted Eichler cocycle evaluated at the identity adele is

`α A 1 = ½ (P (A i) - J_* P (-conj (A i)))`,   `P = LevelThreePeriodPrimitive.primitive (n + 1) f`,

the holomorphic Eichler integral of `f` against `(X₀ - z X₁)^{n+1} dz` normalized at `i`.  This is the
level-three version of `EichlerInput.eichlerCocycle_one_eq_formula`; the real reflection `J` fixes the
scalar function because the vector is fixed by the reflection `diag(-1, 1) ∈ Γ₁'(3)`
(`levelThree_realization_reflection`).

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.SourceConstruction

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Manifold
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.AnalyticClasses
open TernaryPeriodPolynomials.PlaneEisensteinContinuation
open TernaryPeriodPolynomials.TwistedSource
open TernaryPeriodPolynomials.LevelThree

/-- The scalar weighted realization of a level-three vector is invariant under the real reflection
`J` on the right of the base point. -/
theorem l3p_scalar_J (σ : CuspidalRepresentation) (halfWeight : ℤ) (v : σ.smooth)
    (hv : v.val ∈ MultiplicityOne.levelThreeValues σ) (w : ℂ) :
    cuspScalarWeightedRealization σ halfWeight v (1 * atInfinity UpperHalfPlane.J) w =
      cuspScalarWeightedRealization σ halfWeight v 1 w := by
  unfold cuspScalarWeightedRealization cuspScalarAffineRealization
  simp only [one_mul]
  rw [← atInfinity_mul, MultiplicityOne.levelThree_realization_reflection σ v hv]

/-- On the upper half plane the scalar weighted realization at the identity is the function `f`. -/
theorem l3p_scalar_one_eq {σ : CuspidalRepresentation} {halfWeight : ℤ} {v : σ.smooth}
    {f : UpperHalfPlane → ℂ} (hf : f = cuspScalarWeightedLinear σ halfWeight 1 v) {w : ℂ}
    (hz : 0 < w.im) :
    cuspScalarWeightedRealization σ halfWeight v 1 w = f (UpperHalfPlane.ofComplex w) := by
  have value := congrFun hf (UpperHalfPlane.ofComplex w)
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz] at value
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz]
  exact value.symm

/-- **The level-three sign-twisted Eichler cocycle at the identity adele in terms of the classical
primitive.** -/
theorem l3p_alpha_one_eq_formula {σ : CuspidalRepresentation} {n : ℕ} (I : L3Input σ n)
    (stages : AnalyticScalar.ContinuousStages σ) {f : UpperHalfPlane → ℂ}
    (hf : f = cuspScalarWeightedLinear σ I.halfWeight 1 I.vector)
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
  have holomorphic : ∀ h, DifferentiableOn ℂ (endpointScalar σ I.halfWeight I.vector h)
      {z : ℂ | 0 < z.im} := fun h =>
    MultiplicityOne.cuspScalarWeightedRealization_holomorphic σ I.halfWeight I.vector
      I.vector_level I.rotation I.holomorphic h
  have first : eichlerPeriod n (endpointScalar σ I.halfWeight I.vector) (basePoint A) 1 =
      LevelThreePeriodPrimitive.primitive (n + 1) f (basePoint A) :=
    l3p_eichlerPeriod_eq_primitive n hfd (endpointScalar σ I.halfWeight I.vector) holomorphic 1
      (fun w hz => l3p_scalar_one_eq hf hz) positive
  have second : eichlerPeriod n (endpointScalar σ I.halfWeight I.vector)
      (binaryComplexReflection (basePoint A)) (1 * atInfinity UpperHalfPlane.J) =
        LevelThreePeriodPrimitive.primitive (n + 1) f (binaryComplexReflection (basePoint A)) :=
    l3p_eichlerPeriod_eq_primitive n hfd (endpointScalar σ I.halfWeight I.vector) holomorphic
      (1 * atInfinity UpperHalfPlane.J)
      (fun w hz => (l3p_scalar_J σ I.halfWeight I.vector I.vector_level w).trans
        (l3p_scalar_one_eq hf hz)) reflected_positive
  rw [congrFun (I.alpha_eq_eichlerNormalTw stages A) 1]
  unfold eichlerNormalTw
  rw [binaryAmbientRepresentation_apply_of_unimodular unimodular, first, second]

end TernaryPeriodPolynomials.SourceConstruction

end
