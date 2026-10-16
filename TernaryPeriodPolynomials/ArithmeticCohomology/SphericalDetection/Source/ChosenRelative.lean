module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Source.HomogeneousNormalization
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Source.BinaryAnalytic

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem sourcePlaneLevelGroupCocycle_one_of_diagonal {degree : ℕ} (data : InducingData degree)
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data .plane source)
    (diagonal : ∀ vertex argument, source (fun _ => vertex) argument = 0) (first : RealPlaneGroup) :
    sourcePlaneLevelGroupCocycle data source cocycle (first, 1) = 0 := by
  apply Subtype.ext
  apply Subtype.ext
  funext argument
  change (sourcePlaneGroupCocycle data source cocycle (first, 1)).val argument = 0
  rw [sourcePlaneGroupCocycle_apply, map_one, mul_one,
    sourceCocycle_repeated_last data .plane source cocycle diagonal, smul_zero]

theorem sourcePlaneNormalizedGroupCocycle_eq_of_diagonal {degree : ℕ} (data : InducingData degree)
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data .plane source)
    (diagonal : ∀ vertex argument, source (fun _ => vertex) argument = 0) :
    sourcePlaneNormalizedGroupCocycle data source cocycle = sourcePlaneLevelGroupCocycle data source cocycle := by
  apply groupCohomology.cocycles₂_ext
  intro first second
  rw [sourcePlaneNormalizedGroupCocycle, unitNormalizedTwoCocycle_apply,
    sourcePlaneLevelGroupCocycle_one_of_diagonal data source cocycle diagonal, sub_zero]

/-- Retain the actual radical correction along with the regular relative representative. -/
theorem sourcePlaneLevelGroupCocycle_exists_chosen_relative {degree : ℕ} {index : Type} [Fintype index]
    (positive : 0 < degree) (odd : Odd degree) (data : InducingData degree) (trivial : data.chi = trivialCharacter)
    (basis : Module.Basis index ℂ (HomogeneousPoly degree))
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data .plane source)
    (diagonal : ∀ vertex argument, source (fun _ => vertex) argument = 0) :
    ∃ (primitive : RealPlaneRadical → realPlaneLevelCuspidalRep degree data.cusp data.chi)
      (relative : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
        (realPlaneLevelCuspidalRep degree data.cusp data.chi)),
      (∀ center : Fin 2 → ℝ, AnalyticAt ℝ (fun point : BinaryRealMatrix × (Fin 2 → ℝ) =>
        binaryHilbertTranslation data.cusp (atInfinity (invertibleMatrix point.1))
          (cuspidalTensorHilbertEmbedding data.cusp basis (primitive (Multiplicative.ofAdd point.2)).val)) (1, center)) ∧
      relative.val = sourcePlaneLevelGroupCocycle data source cocycle -
        twoBoundaryCycle _ (realPlanePrimitiveExtension _ primitive) ∧
      groupCohomology.H2π _ relative.val = groupCohomology.H2π _ (sourcePlaneLevelGroupCocycle data source cocycle) ∧
      RealPlaneLevelMixedRegular degree data.cusp data.chi basis relative ∧
      RealPlaneLevelMixedAnalytic degree data.cusp data.chi basis relative := by
  obtain ⟨primitive, analytic, relative, formula, same_class⟩ :=
    sourcePlaneLevelGroupCocycle_exists_analytic_relative positive odd data trivial basis source cocycle
  have regular := cuspidalTensorFamily_contDiff_of_orbital data.cusp basis
    (fun point : Fin 2 → ℝ => (primitive (Multiplicative.ofAdd point)).val) analytic
  refine ⟨primitive, relative, analytic, ?_, same_class,
    sourcePlaneRelative_mixed_hilbertContDiff data basis source cocycle primitive (regular.of_le le_top) relative formula,
    sourcePlaneRelative_mixed_analyticAt_one data trivial basis source cocycle primitive analytic relative formula⟩
  exact formula.trans (congrArg (· - twoBoundaryCycle _ (realPlanePrimitiveExtension _ primitive))
    (sourcePlaneNormalizedGroupCocycle_eq_of_diagonal data source cocycle diagonal))

end TernaryPeriodPolynomials.SphericalDetection.Helpers
