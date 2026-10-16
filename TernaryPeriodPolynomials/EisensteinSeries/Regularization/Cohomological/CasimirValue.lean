module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Binary.GroupCocycleCoboundary

@[expose] public section


open GeneralEisenstein

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem cohomological_casimir_value {cusp : CuspidalRepresentation} {degree : ℕ}
    (cohomological : Cohomological cusp degree) :
    cuspCasimirOperator cusp =
      (((degree : ℂ) + 1) * ((degree : ℂ) + 3)) • (1 : Module.End ℂ cusp.smooth) := by
  obtain ⟨scalar, casimir⟩ := cohomological_casimir_scalar cohomological
  rcases eq_or_ne (scalar : ℂ) (((degree : ℂ) + 1) * ((degree : ℂ) + 3)) with equal | distinct
  · rw [casimir, equal]
  · obtain ⟨cocycle, smooth, finite, identity, nontrivial⟩ := cohomological_lifted_cocycle cohomological
    exact False.elim (nontrivial
      (binary_group_cocycle_coboundary_of_distinct_casimir cusp degree scalar casimir distinct cocycle smooth finite identity))

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
