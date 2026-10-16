module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Cohomological.CasimirValue
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Cusp.CasimirWeights

@[expose] public section


open GeneralEisenstein

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem cohomological_rotation_weight_gap {cusp : CuspidalRepresentation} {degree : ℕ}
    (cohomological : Cohomological cusp degree) (weight : ℝ) (vector : cusp.smooth)
    (nonzero : vector ≠ 0)
    (rotation : cuspRotationOperator cusp vector = (Complex.I * (weight : ℂ)) • vector) :
    (degree : ℝ) + 3 ≤ |weight| := by
  have eigenvector : cuspCasimirOperator cusp vector =
      (↑(((degree : ℝ) + 1) * ((degree : ℝ) + 3)) : ℂ) • vector := by
    rw [cohomological_casimir_value cohomological, LinearMap.smul_apply, Module.End.one_apply]
    push_cast
    rfl
  have bound := cuspCasimir_bound_of_weight cusp weight (((degree : ℝ) + 1) * ((degree : ℝ) + 3))
    vector nonzero rotation eigenvector
  by_contra failure
  have positive : 0 < ((degree : ℝ) + 3 - |weight|) * (|weight| + (degree : ℝ) + 1) :=
    mul_pos (by linarith [not_le.mp failure]) (by positivity)
  nlinarith [sq_abs weight]

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
