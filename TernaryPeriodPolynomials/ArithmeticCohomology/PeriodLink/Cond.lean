module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Source.GoodPlaneRealization
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Source.LevelThreeEichlerMain
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Even.PlanePeriodCore
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.L3PeriodAlpha
public import TernaryPeriodPolynomials.ArithmeticCohomology.MultiplicityOne.DictionaryInjective

@[expose] public section


/-!
# The level-three Eichler cocycle is the classical period cocycle (good plane)

Formalized by Claude Sonnet 5.5 (AxiomCode).

Untwisted twin of `SourceConstruction.l3Period_vector_eq_zero` for CRL's level-three
Eichler datum `lteData D stages` of an Eichler input `D : L3Input σ n`.

* `lte_alpha_one_eq_formula`: at the identity adele the untwisted Eichler cocycle is
  `½ (P (A i) + J_* P (-conj (A i)))`, `P = LevelThreePeriodPrimitive.primitive (n + 1) f`, for the
  classical form `f` of the vector;
* `lte_vector_eq_zero`: if `levelPeriodMap (n + 1) (-1)` is injective and the values
  `A ↦ α(A_ℝ) 1` on `Γ₁'(3)` are a coboundary in `det⁻¹ Sym^{n+1}`, then `D.vector = 0`
  (the comparison `α(A_ℝ) 1 = levelPlus (n + 1) (-1) (periodCocycle (n + 1) (-1) f)` is
  `EvenLevelThree.l3pp_levelPlus_eq_alpha`);
* `levelThreePeriodNonvanishing_of_injective`: CRL's input `LevelThreePeriodNonvanishing n` from
  the injectivity of `levelPeriodMap (n + 1) (-1)`.
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous Matrix
open scoped Manifold
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.AnalyticClasses
open TernaryPeriodPolynomials.PlaneEisensteinContinuation
open TernaryPeriodPolynomials.LevelThree
open TernaryPeriodPolynomials.LevelThree.ParabolicBounds (levelRep)
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
  (binaryArithmeticLevel)
open TernaryPeriodPolynomials.SourceConstruction
  (L3Input l3p_scalar_J l3p_scalar_one_eq l3p_eichlerPeriod_eq_primitive l3p_exists_S_cast)
open TernaryPeriodPolynomials.LevelThreeSource
  (lteData lteA lteA_eq_eichlerNormal LevelThreePeriodNonvanishing levelThreeEichlerInput
    levelThreeStages levelThreeCusp_of_classical)

namespace TernaryPeriodPolynomials.PeriodLink

/-- **The level-three untwisted Eichler cocycle at the identity adele in terms of the classical
primitive.** -/
theorem lte_alpha_one_eq_formula {σ : CuspidalRepresentation} {n : ℕ} (D : L3Input σ n)
    (stages : AnalyticScalar.ContinuousStages σ) {f : UpperHalfPlane → ℂ}
    (hf : f = cuspScalarWeightedLinear σ D.halfWeight 1 D.vector)
    (hfd : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (A : BinaryRealGL) :
    (lteData D stages).α A 1 = (2 : ℂ)⁻¹ •
      (LevelThreePeriodPrimitive.primitive (n + 1) f (basePoint A) +
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
  have holomorphic : ∀ h, DifferentiableOn ℂ (endpointScalar σ D.halfWeight D.vector h)
      {z : ℂ | 0 < z.im} := fun h =>
    MultiplicityOne.cuspScalarWeightedRealization_holomorphic σ D.halfWeight D.vector
      D.vector_level D.rotation D.holomorphic h
  have first : eichlerPeriod n (endpointScalar σ D.halfWeight D.vector) (basePoint A) 1 =
      LevelThreePeriodPrimitive.primitive (n + 1) f (basePoint A) :=
    l3p_eichlerPeriod_eq_primitive n hfd (endpointScalar σ D.halfWeight D.vector) holomorphic 1
      (fun w hz => l3p_scalar_one_eq hf hz) positive
  have second : eichlerPeriod n (endpointScalar σ D.halfWeight D.vector)
      (binaryComplexReflection (basePoint A)) (1 * atInfinity UpperHalfPlane.J) =
        LevelThreePeriodPrimitive.primitive (n + 1) f (binaryComplexReflection (basePoint A)) :=
    l3p_eichlerPeriod_eq_primitive n hfd (endpointScalar σ D.halfWeight D.vector) holomorphic
      (1 * atInfinity UpperHalfPlane.J)
      (fun w hz => (l3p_scalar_J σ D.halfWeight D.vector D.vector_level w).trans
        (l3p_scalar_one_eq hf hz)) reflected_positive
  change lteA D A 1 = _
  rw [congrFun (lteA_eq_eichlerNormal D stages A) 1, eichlerNormal_def,
    binaryAmbientRepresentation_apply_of_unimodular unimodular, first, second]

/-- **A coboundary level-three Levi period class forces the Eichler input to vanish** (given the
injectivity of the period map `levelPeriodMap (n + 1) (-1)`). -/
theorem lte_vector_eq_zero {σ : CuspidalRepresentation} {n : ℕ} (D : L3Input σ n)
    (stages : AnalyticScalar.ContinuousStages σ)
    (hper : Function.Injective
      (LevelThreePeriodParity.levelPeriodMap (n + 1) (-1)))
    (hcob : ∃ w₀ : Binary.HomogeneousPoly (n + 1), ∀ A : binaryArithmeticLevel,
      (lteData D stages).α (GeneralLinearGroup.map (Int.castRingHom ℝ) A.val) 1 =
        levelRep (n + 1) (-1) A w₀ - w₀) :
    D.vector = 0 := by
  have negative : D.halfWeight < 0 := by
    have := D.weight
    omega
  have hmem : D.vector ∈ MultiplicityOne.levelThreeClassicalVectors σ D.halfWeight :=
    MultiplicityOne.levelThreeClassicalVectors_mem_of_holomorphic σ D.halfWeight
      D.vector D.vector_level D.rotation
      (MultiplicityOne.cuspScalarWeightedRealization_holomorphic σ D.halfWeight D.vector
        D.vector_level D.rotation D.holomorphic 1)
  have wt : -2 * D.halfWeight = ((n + 1 : ℕ) : ℤ) + 2 := by
    have := D.weight
    push_cast
    omega
  obtain ⟨g, hg⟩ := l3p_exists_S_cast (n + 1) wt
    (MultiplicityOne.levelThreeForm σ D.halfWeight negative D.vector hmem)
  have hf : (g : UpperHalfPlane → ℂ) = cuspScalarWeightedLinear σ D.halfWeight 1 D.vector :=
    hg.trans (MultiplicityOne.levelThreeForm_coe σ D.halfWeight negative D.vector hmem)
  have hfd : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (g : UpperHalfPlane → ℂ) :=
    LevelThreePeriodCocycle.form_holo g
  have hα : EvenLevelThree.L3PlanePeriodFormula (lteData D stages) ⇑g := fun K =>
    lte_alpha_one_eq_formula D stages hf hfd K
  have hmap0 := EvenLevelThree.l3pp_levelPeriodMap_eq_zero (lteData D stages) g hα hcob
  have hg0 : g = 0 := hper (by rw [hmap0, map_zero])
  by_contra hv0
  obtain ⟨pt, hpt⟩ := MultiplicityOne.levelThree_scalar_exists_nonzero σ
    D.central_positive D.halfWeight D.vector hmem hv0
  apply hpt
  have e1 : (g : UpperHalfPlane → ℂ) pt =
      cuspScalarWeightedRealization σ D.halfWeight D.vector 1 pt := congrFun hf pt
  rw [← e1]
  simp [hg0]

/-- **Level-three period nonvanishing in degree `n`**, from the injectivity of the parity-projected
period map `levelPeriodMap (n + 1) (-1)` of `Γ₁(3)`: the Eichler cocycle of a nonzero holomorphic
level-three vector of weight `n + 3` is not a crossed coboundary on `Γ₁'(3)`. -/
theorem levelThreePeriodNonvanishing_of_injective (n : ℕ)
    (hinj : Function.Injective (LevelThreePeriodParity.levelPeriodMap (n + 1) (-1))) :
    LevelThreePeriodNonvanishing n := by
  intro σ coh halfWeight hw v hv hv0 hcob
  obtain ⟨w, hw'⟩ := hcob
  apply hv0
  exact lte_vector_eq_zero
    (levelThreeEichlerInput coh (levelThreeCusp_of_classical hv hv0) halfWeight hw v hv)
    (levelThreeStages coh) hinj ⟨w, fun A => hw' A⟩

end TernaryPeriodPolynomials.PeriodLink

end
