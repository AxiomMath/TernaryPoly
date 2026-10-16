module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Principal.LowestFormDetection

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

theorem cuspPrincipalLowest_finiteDimensional
    {cusp : CuspidalRepresentation} {degree : ℕ} (cohomological : Cohomological cusp degree)
    (weight : ℕ) (weight_positive : 0 < weight) :
    FiniteDimensional ℂ (cuspPrincipalLowestSubmodule cusp weight) := by
  obtain ⟨representatives, detects⟩ :=
    cuspPrincipalLowestForm_finite_detection cohomological weight weight_positive
  let forms : cuspPrincipalLowestSubmodule cusp weight →ₗ[ℂ]
      (representatives → CuspForm binaryRealPrincipalLevel (weight : ℤ)) :=
    LinearMap.pi (fun matrix => (cuspPrincipalLowestFormLinear cohomological weight weight_positive).comp
      (cuspPrincipalLowestIntegralAction cusp weight matrix.val))
  apply FiniteDimensional.of_injective forms
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro vector zero
  apply detects vector
  intro matrix member
  exact congrFun zero ⟨matrix, member⟩

theorem cuspPrincipalLowest_scalar_bound
    {cusp : CuspidalRepresentation} {degree : ℕ} (cohomological : Cohomological cusp degree)
    (weight : ℕ) (weight_positive : 0 < weight) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ vector : cuspPrincipalLowestSubmodule cusp weight,
        ‖cuspBoundedRealization cusp vector.val‖ ≤ constant * ‖vector.val.val‖ := by
  let : FiniteDimensional ℂ (cuspPrincipalLowestSubmodule cusp weight) :=
    cuspPrincipalLowest_finiteDimensional cohomological weight weight_positive
  let realization := (cuspBoundedRealization cusp).comp (cuspPrincipalLowestSubmodule cusp weight).subtype
  let continuousRealization := realization.toContinuousLinearMap
  exact ⟨‖continuousRealization‖, continuousRealization.opNorm_nonneg,
    fun vector => continuousRealization.le_opNorm vector⟩

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
