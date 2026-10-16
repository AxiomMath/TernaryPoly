module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Arithmetic.StabilizerEdge
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Split.CohomologyExactness

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix CategoryTheory

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem identityPlaneBinaryEdge_kernel (degree : ℕ) :
    (identityPlaneBinaryEdge degree).ker =
      (splitInvariantInflationKernel identityPlaneSplitting (identityPlaneCoefficientRep degree)).range := by
  rw [splitCohomologyEdge_exact]
  apply LinearMap.ker_comp_of_ker_eq_bot
  exact LinearMap.ker_eq_bot.mpr (ConcreteCategory.bijective_of_isIso (identityPlaneLeviCohomologyIso degree).hom).injective

theorem goodLineBinaryEdge_kernel (degree : ℕ) (positive : 0 < degree) :
    (goodLineBinaryEdge degree positive).ker =
      (splitInvariantInflationKernel goodLineSplitting (goodLineCoefficientRep degree)).range := by
  rw [splitCohomologyEdge_exact]
  apply LinearMap.ker_comp_of_ker_eq_bot
  exact LinearMap.ker_eq_bot.mpr (ConcreteCategory.bijective_of_isIso (goodLineLeviCohomologyIso degree positive).hom).injective

theorem identityPlaneBinaryEdge_zero_iff_inflation (degree : ℕ)
    (cohomology : (twoCohomologyRestriction identityPlaneRadicalInclusion (identityPlaneCoefficientRep degree)).ker) :
    identityPlaneBinaryEdge degree cohomology = 0 ↔
      ∃ levi_class : groupCohomology.H2 (splitInvariantRepresentation identityPlaneSplitting (identityPlaneCoefficientRep degree)),
        splitInvariantInflation identityPlaneSplitting (identityPlaneCoefficientRep degree) levi_class = cohomology.val := by
  change cohomology ∈ (identityPlaneBinaryEdge degree).ker ↔ _
  rw [identityPlaneBinaryEdge_kernel]
  constructor
  · rintro ⟨levi_class, equality⟩
    exact ⟨levi_class, congrArg Subtype.val equality⟩
  · rintro ⟨levi_class, equality⟩
    exact ⟨levi_class, Subtype.ext equality⟩

theorem goodLineBinaryEdge_zero_iff_inflation (degree : ℕ) (positive : 0 < degree)
    (cohomology : (twoCohomologyRestriction goodLineRadicalInclusion (goodLineCoefficientRep degree)).ker) :
    goodLineBinaryEdge degree positive cohomology = 0 ↔
      ∃ levi_class : groupCohomology.H2 (splitInvariantRepresentation goodLineSplitting (goodLineCoefficientRep degree)),
        splitInvariantInflation goodLineSplitting (goodLineCoefficientRep degree) levi_class = cohomology.val := by
  change cohomology ∈ (goodLineBinaryEdge degree positive).ker ↔ _
  rw [goodLineBinaryEdge_kernel]
  constructor
  · rintro ⟨levi_class, equality⟩
    exact ⟨levi_class, congrArg Subtype.val equality⟩
  · rintro ⟨levi_class, equality⟩
    exact ⟨levi_class, Subtype.ext equality⟩

theorem identityPlaneBinaryEdge_injective_of_invariant_H2_zero (degree : ℕ)
    (vanishing : ∀ cohomology : groupCohomology.H2
      (splitInvariantRepresentation identityPlaneSplitting (identityPlaneCoefficientRep degree)), cohomology = 0) :
    Function.Injective (identityPlaneBinaryEdge degree) :=
  (ConcreteCategory.bijective_of_isIso (identityPlaneLeviCohomologyIso degree).hom).injective.comp
    (splitCohomologyEdge_injective_of_invariant_H2_zero identityPlaneSplitting (identityPlaneCoefficientRep degree) vanishing)

theorem goodLineBinaryEdge_injective_of_invariant_H2_zero (degree : ℕ) (positive : 0 < degree)
    (vanishing : ∀ cohomology : groupCohomology.H2
      (splitInvariantRepresentation goodLineSplitting (goodLineCoefficientRep degree)), cohomology = 0) :
    Function.Injective (goodLineBinaryEdge degree positive) :=
  (ConcreteCategory.bijective_of_isIso (goodLineLeviCohomologyIso degree positive).hom).injective.comp
    (splitCohomologyEdge_injective_of_invariant_H2_zero goodLineSplitting (goodLineCoefficientRep degree) vanishing)

end TernaryPeriodPolynomials.SphericalDetection.Helpers
