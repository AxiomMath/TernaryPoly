module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Real.PlaneLevelAnalyticPrimitive
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Real.PlanePrimitiveExtension

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem sourcePlaneNormalizedGroupCocycle_exists_analytic_radical_primitive {degree : ℕ} {index : Type} [Fintype index]
    (positive : 0 < degree) (odd : Odd degree) (data : InducingData degree) (trivial : data.chi = trivialCharacter)
    (basis : Module.Basis index ℂ (HomogeneousPoly degree))
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data .plane source) :
    ∃ primitive : RealPlaneRadical → cuspidalTensorValues data.cusp (HomogeneousPoly degree),
      (∀ element, primitive element ∈ cuspidalTensorFiniteLevel data.cusp (HomogeneousPoly degree)) ∧
      (∀ center : Fin 2 → ℝ, AnalyticAt ℝ (fun point : BinaryRealMatrix × (Fin 2 → ℝ) =>
        binaryHilbertTranslation data.cusp (atInfinity (invertibleMatrix point.1))
          (cuspidalTensorHilbertEmbedding data.cusp basis (primitive (Multiplicative.ofAdd point.2)))) (1, center)) ∧
      ∀ first second,
        cuspidalTensorMap (V := HomogeneousPoly degree) (W := HomogeneousPoly degree) data.cusp
          ((realUpperRadicalRep degree).ρ first) (primitive second) - primitive (first * second) + primitive first =
            (sourcePlaneNormalizedGroupCocycle data source cocycle (SemidirectProduct.inl first, SemidirectProduct.inl second)).val :=
  realPlaneLevelTwoCocycle_exists_analytic_radical_primitive degree positive odd data.cusp data.chi trivial basis
    (sourcePlaneNormalizedGroupCocycle data source cocycle) (sourcePlaneNormalizedGroupCocycle_unit data source cocycle)
    (sourcePlaneNormalizedGroupCocycle_radical_orbital_analyticAt data basis source cocycle)

theorem sourcePlaneLevelGroupCocycle_exists_analytic_relative {degree : ℕ} {index : Type} [Fintype index]
    (positive : 0 < degree) (odd : Odd degree) (data : InducingData degree) (trivial : data.chi = trivialCharacter)
    (basis : Module.Basis index ℂ (HomogeneousPoly degree))
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data .plane source) :
    ∃ primitive : RealPlaneRadical → realPlaneLevelCuspidalRep degree data.cusp data.chi,
      (∀ center : Fin 2 → ℝ, AnalyticAt ℝ (fun point : BinaryRealMatrix × (Fin 2 → ℝ) =>
        binaryHilbertTranslation data.cusp (atInfinity (invertibleMatrix point.1))
          (cuspidalTensorHilbertEmbedding data.cusp basis (primitive (Multiplicative.ofAdd point.2)).val)) (1, center)) ∧
      ∃ relative : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
          (realPlaneLevelCuspidalRep degree data.cusp data.chi),
        relative.val = sourcePlaneNormalizedGroupCocycle data source cocycle -
          twoBoundaryCycle _ (realPlanePrimitiveExtension _ primitive) ∧
        groupCohomology.H2π _ relative.val = groupCohomology.H2π _ (sourcePlaneLevelGroupCocycle data source cocycle) := by
  obtain ⟨primitive, fixed, analytic, boundary⟩ :=
    sourcePlaneNormalizedGroupCocycle_exists_analytic_radical_primitive positive odd data trivial basis source cocycle
  let levelPrimitive : RealPlaneRadical → realPlaneLevelCuspidalRep degree data.cusp data.chi :=
    fun radical => ⟨primitive radical, fixed radical⟩
  have levelBoundary (first second : RealPlaneRadical) :
      (realPlaneLevelCuspidalRep degree data.cusp data.chi).ρ (SemidirectProduct.inl first) (levelPrimitive second) -
          levelPrimitive (first * second) + levelPrimitive first =
        sourcePlaneNormalizedGroupCocycle data source cocycle (SemidirectProduct.inl first, SemidirectProduct.inl second) := by
    apply Subtype.ext
    change ((realPlaneLevelCuspidalRep degree data.cusp data.chi).ρ (SemidirectProduct.inl first) (levelPrimitive second)).val -
      primitive (first * second) + primitive first = _
    rw [realPlaneLevelCuspidalRep_radical_of_trivial degree data.cusp data.chi trivial]
    exact boundary first second
  refine ⟨levelPrimitive, analytic, realPlaneRelativeCycle _ _ levelPrimitive levelBoundary, rfl, ?_⟩
  rw [realPlaneRelativeCycle_H2, sourcePlaneNormalizedGroupCocycle_H2]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
