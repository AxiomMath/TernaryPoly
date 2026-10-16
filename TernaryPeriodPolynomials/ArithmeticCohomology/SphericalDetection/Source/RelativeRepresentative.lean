module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Source.AnalyticPrimitive

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem sourcePlaneLevelGroupCocycle_exists_relative {degree : ℕ} {index : Type} [Fintype index]
    (positive : 0 < degree) (odd : Odd degree) (data : InducingData degree) (trivial : data.chi = trivialCharacter)
    (basis : Module.Basis index ℂ (HomogeneousPoly degree))
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data .plane source) :
    ∃ primitive : RealPlaneRadical → realPlaneLevelCuspidalRep degree data.cusp data.chi,
      ContDiff ℝ (↑(⊤ : ℕ∞)) (fun point : Fin 2 → ℝ =>
        cuspidalTensorHilbertEmbedding data.cusp basis (primitive (Multiplicative.ofAdd point)).val) ∧
      ∃ relative : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
          (realPlaneLevelCuspidalRep degree data.cusp data.chi),
        relative.val = sourcePlaneNormalizedGroupCocycle data source cocycle -
          twoBoundaryCycle _ (realPlanePrimitiveExtension _ primitive) ∧
        groupCohomology.H2π _ relative.val = groupCohomology.H2π _ (sourcePlaneLevelGroupCocycle data source cocycle) := by
  obtain ⟨primitive, analytic, relative, formula, same_class⟩ :=
    sourcePlaneLevelGroupCocycle_exists_analytic_relative positive odd data trivial basis source cocycle
  have regular := cuspidalTensorFamily_contDiff_of_orbital data.cusp basis
    (fun point : Fin 2 → ℝ => (primitive (Multiplicative.ofAdd point)).val) analytic
  exact ⟨primitive, regular.of_le le_top, relative, formula, same_class⟩

end TernaryPeriodPolynomials.SphericalDetection.Helpers
