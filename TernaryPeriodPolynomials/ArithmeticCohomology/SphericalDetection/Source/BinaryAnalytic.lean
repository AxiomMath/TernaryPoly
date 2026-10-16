module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Source.RelativeLeviAnalytic
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Real.PlaneLevelBinaryAnalytic

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem sourcePlaneLevelGroupCocycle_exists_binary_analytic_relative {degree : ℕ} {index : Type} [Fintype index]
    (positive : 0 < degree) (odd : Odd degree) (data : InducingData degree) (trivial : data.chi = trivialCharacter)
    (basis : Module.Basis index ℂ (HomogeneousPoly degree))
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data .plane source) :
    ∃ relative : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
        (realPlaneLevelCuspidalRep degree data.cusp data.chi),
      groupCohomology.H2π _ relative.val = groupCohomology.H2π _ (sourcePlaneLevelGroupCocycle data source cocycle) ∧
      RealPlaneLevelMixedRegular degree data.cusp data.chi basis relative ∧
      RealPlaneLevelMixedAnalytic degree data.cusp data.chi basis relative := by
  obtain ⟨primitive, analytic, relative, formula, same_class⟩ :=
    sourcePlaneLevelGroupCocycle_exists_analytic_relative positive odd data trivial basis source cocycle
  have regular := cuspidalTensorFamily_contDiff_of_orbital data.cusp basis
    (fun point : Fin 2 → ℝ => (primitive (Multiplicative.ofAdd point)).val) analytic
  exact ⟨relative, same_class,
    sourcePlaneRelative_mixed_hilbertContDiff data basis source cocycle primitive (regular.of_le le_top) relative formula,
    sourcePlaneRelative_mixed_analyticAt_one data trivial basis source cocycle primitive analytic relative formula⟩

end TernaryPeriodPolynomials.SphericalDetection.Helpers
