module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Normalized.Continuation
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.LargeDegreeRegularization
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.SmallDegreeRegularization
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Boundary.ResidueVanishing

@[expose] public section


open GeneralEisenstein
open Homogeneous Adelic

namespace TernaryPeriodPolynomials.EisensteinRegularization

theorem eisenstein_regularization : ∀ n : ℕ, 0 < n → ∀ D : InducingData n, D.chi = trivialCharacter →
    ∀ F : ℂ → AdelicGL → ℂ, IsFlatSection D F →
    ∀ E : ℂ → AdelicGL → ℂ, IsEisensteinContinuation F E →
    ∃ E' : ℂ → AdelicGL → ℂ,
      IsEisensteinContinuation F E' ∧ SameOffCohomologicalPoint E E' ∧
      ∀ g, AnalyticAt ℂ (fun z => E' z g) cohomologicalPoint := by
  intro degree degree_positive inducingData character_trivial sectionFamily flat_family
    continuation continuation_spec
  by_cases degree_large : 3 < degree
  · exact Helpers.regularization_of_large_degree degree_large flat_family continuation_spec
  have degree_small : degree ≤ 3 := Nat.le_of_not_gt degree_large
  by_cases degree_smaller : degree < 3
  · exact Helpers.regularization_of_small_degree degree_smaller flat_family continuation_spec
  have degree_three : degree = 3 := by omega
  subst degree
  apply Helpers.regularization_of_unitaryNormalize_order (degree := 3) continuation_spec
  intro groupElement
  apply (Helpers.normalizedBoundaryResidue_eq_zero_iff_order_nonnegative
    flat_family continuation_spec groupElement).mp
  exact Helpers.normalizedBoundaryResidue_zero flat_family continuation_spec groupElement

end TernaryPeriodPolynomials.EisensteinRegularization
