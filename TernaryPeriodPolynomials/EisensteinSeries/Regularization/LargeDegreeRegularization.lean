module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.SectionScalarBounds
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Scalar.ProfileRegularization

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem normalized_scalar_sum_analytic
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (matrix : AdelicGL) :
    AnalyticOnNhd ℂ
      (fun parameter => ∑' flag, eisensteinSummand (unitaryNormalize degree family) parameter matrix flag)
      {parameter : ℂ | 3 / 2 < parameter.re} ∧
    ∀ parameter : ℂ, 3 / 2 < parameter.re →
      Summable (eisensteinSummand (unitaryNormalize degree family) parameter matrix) :=
  normalized_scalar_flag_sum_analytic_of_profile_bounds flat
    (normalizedScalarProfile_compact_bound flat) matrix

theorem regularization_of_large_degree
    {degree : ℕ} (degree_large : 3 < degree) {inducingData : InducingData degree}
    {family continuation : ℂ → AdelicGL → ℂ} (flat : IsFlatSection inducingData family)
    (continuation_spec : IsEisensteinContinuation family continuation) :
    ∃ repaired : ℂ → AdelicGL → ℂ,
      IsEisensteinContinuation family repaired ∧ SameOffCohomologicalPoint continuation repaired ∧
        ∀ matrix, AnalyticAt ℂ (fun parameter => repaired parameter matrix) cohomologicalPoint :=
  regularization_of_large_degree_profile_bounds degree_large flat continuation_spec
    (normalizedScalarProfile_compact_bound flat)

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
