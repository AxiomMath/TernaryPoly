module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Cohomological.HilbertRotationGap

@[expose] public section


open GeneralEisenstein

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem cohomological_casimir_eigenvector {cusp : CuspidalRepresentation} {degree : ℕ}
    (cohomological : Cohomological cusp degree) (vector : cusp.smooth) :
    cuspCasimirOperator cusp vector = (↑(((degree : ℝ) + 1) * ((degree : ℝ) + 3)) : ℂ) • vector := by
  rw [cohomological_casimir_value cohomological, LinearMap.smul_apply, Module.End.one_apply]
  push_cast
  rfl

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
