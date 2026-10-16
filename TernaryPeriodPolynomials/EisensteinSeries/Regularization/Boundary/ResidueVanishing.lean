module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Residue.Continuity
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Residue.Correlation
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Residue.SpecialLinearDetection
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.InvariantDomainDetection

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

theorem normalizedBoundaryResidue_zero
    {degree : ℕ} {inducingData : InducingData degree} {family continuation : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (continuation_spec : IsEisensteinContinuation family continuation)
    (matrix : AdelicGL) : normalizedBoundaryResidue degree continuation matrix = 0 := by
  apply normalizedBoundaryResidue_zero_of_specialLinear_slices flat continuation_spec _ matrix
  intro integral special
  have representative := normalizedBoundaryResiduePrincipalL2_coe flat continuation_spec integral
  rw [normalizedBoundaryResiduePrincipalL2_zero flat continuation_spec integral] at representative
  have quotient_zero : ∀ᵐ point ∂principalSpecialLinearQuotientMeasure,
      normalizedBoundaryResiduePrincipalQuotient flat continuation_spec integral point = 0 := by
    filter_upwards [representative, Lp.coeFn_zero (E := ℂ) (p := 2) (μ := principalSpecialLinearQuotientMeasure)]
      with point value zero
    exact value.symm.trans zero
  have slice_zero := continuous_invariant_zero_of_fundamental_domain
    principalRealSpecialLinearDomain_measurable principalRealSpecialLinearDomain_fundamental
    (normalizedBoundaryResidue_real_integral_slice_continuous flat continuation_spec integral)
    (normalizedBoundaryResidue_principal_slice_invariant flat continuation_spec integral)
    (ae_of_ae_map measurable_quotient_mk''.aemeasurable quotient_zero)
  exact congrFun slice_zero special

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
