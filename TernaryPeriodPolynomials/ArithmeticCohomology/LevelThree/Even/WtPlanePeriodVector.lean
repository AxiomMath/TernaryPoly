module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Even.PlanePeriodCore
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Even.WtPeriodAlpha
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Even.WtL3PlaneB
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Even.WtForm

@[expose] public section


/-!
# At the good plane a vanishing Levi period class forces the weight vector to vanish

Formalized by Claude Sonnet 5.5 (AxiomCode).

Plane twin of `WtPeriodAlpha` and `WtPeriodVector` for the untwisted Levi cocycle datum
`lteDataWt I stages` of `I : L3InputWt σ n` (integer rotation weight `wt = -(n + 3)`, no parity
hypothesis on `n`).

* `l3pp_alpha_one_eq_formulaWt`: at the identity adele the untwisted Eichler cocycle is
  `½ (P (A i) + J_* P (-conj (A i)))`, `P = LevelThreePeriodPrimitive.primitive (n + 1) f`;
* `l3PlanePeriod_vector_eq_zeroWt`: if the period map `levelPeriodMap (n + 1) (-1)` is injective
  (Eichler–Shimura) and the Levi values `A ↦ α(A_ℝ) 1` are a coboundary in `det⁻¹ Sym^{n+1}`,
  then `I.vector = 0`.
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
open TernaryPeriodPolynomials.LevelThree.ParabolicBounds (levelRep)
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
  (binaryArithmeticLevel)
open TernaryPeriodPolynomials.SourceConstruction
  (l3p_eichlerPeriod_eq_primitive l3p_exists_S_cast)

/-- **The weight-generic level-three untwisted Eichler cocycle at the identity adele in terms of
the classical primitive.** -/
theorem l3pp_alpha_one_eq_formulaWt {σ : CuspidalRepresentation} {n : ℕ} (I : L3InputWt σ n)
    (stages : AnalyticScalar.ContinuousStages σ) {f : UpperHalfPlane → ℂ}
    (hf : f = cuspScalarWeightedLinearWt σ I.wt 1 I.vector)
    (hfd : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (A : BinaryRealGL) :
    (lteDataWt I stages).α A 1 = (2 : ℂ)⁻¹ •
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
  change lteAWt I A 1 = _
  rw [congrFun (lteA_eq_eichlerNormalWt I stages A) 1, eichlerNormal_def,
    binaryAmbientRepresentation_apply_of_unimodular unimodular, first, second]

/-- **At the good plane a coboundary Levi period class forces the weight-generic Eichler input to
vanish** (given the injectivity of the period map `levelPeriodMap (n + 1) (-1)`). -/
theorem l3PlanePeriod_vector_eq_zeroWt {σ : CuspidalRepresentation} {n : ℕ} (I : L3InputWt σ n)
    (stages : AnalyticScalar.ContinuousStages σ)
    (hper : Function.Injective
      (LevelThree.LevelThreePeriodParity.levelPeriodMap (n + 1) (-1)))
    (hcob : ∃ w₀ : Binary.HomogeneousPoly (n + 1), ∀ A : binaryArithmeticLevel,
      (lteDataWt I stages).α (GeneralLinearGroup.map (Int.castRingHom ℝ) A.val) 1 =
        levelRep (n + 1) (-1) A w₀ - w₀) :
    I.vector = 0 := by
  have negative : I.wt < 0 := by
    have := I.weight
    omega
  have hmem : I.vector ∈ levelThreeClassicalVectorsWt σ I.wt := by
    refine ⟨I.vector_level, I.rotation, UpperHalfPlane.mdifferentiable_iff.mpr ?_⟩
    apply (cuspScalarWeightedRealization_holomorphicWt σ stages I.wt I.vector I.fixedLevel
      I.holomorphic 1).congr
    intro point positive
    rw [Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos positive]
    rfl
  have weight : -I.wt = ((n + 1 : ℕ) : ℤ) + 2 := by
    have := I.weight
    push_cast
    omega
  obtain ⟨g, hg⟩ := l3p_exists_S_cast (n + 1) weight
    (levelThreeFormWt σ I.wt negative I.vector hmem)
  have hf : (g : UpperHalfPlane → ℂ) = cuspScalarWeightedLinearWt σ I.wt 1 I.vector :=
    hg.trans (levelThreeForm_coeWt σ I.wt negative I.vector hmem)
  have hfd : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (g : UpperHalfPlane → ℂ) :=
    LevelThree.LevelThreePeriodCocycle.form_holo g
  have hα : L3PlanePeriodFormula (lteDataWt I stages) ⇑g := fun K =>
    l3pp_alpha_one_eq_formulaWt I stages hf hfd K
  have hmap0 := l3pp_levelPeriodMap_eq_zero (lteDataWt I stages) g hα hcob
  have hg0 : g = 0 := hper (by rw [hmap0, map_zero])
  by_contra hv0
  obtain ⟨pt, hpt⟩ := levelThree_scalar_exists_nonzeroWt σ I.central_positive I.wt I.vector hmem
    hv0
  apply hpt
  have e1 : (g : UpperHalfPlane → ℂ) pt = cuspScalarWeightedRealizationWt σ I.wt I.vector 1 pt :=
    congrFun hf pt
  rw [← e1]
  simp [hg0]

end TernaryPeriodPolynomials.EvenLevelThree

end
