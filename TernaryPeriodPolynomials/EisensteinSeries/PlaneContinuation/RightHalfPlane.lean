module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Endpoint.Admissibility

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.RightHalfPlane

theorem summable {degree : ℕ} {data : InducingData degree}
    {sectionFamily : ℂ → AdelicGL → ℂ} (flatSection : IsFlatSection data sectionFamily)
    (point : AdelicGL) (parameter : ℂ) (rightHalfPlane : -(degree : ℝ) / 2 < parameter.re) :
    Summable (eisensteinSummand sectionFamily parameter point) :=
  (EndpointAdmissibility.hasSum flatSection point parameter rightHalfPlane).summable

theorem uniformly_on_strip {degree : ℕ} {data : InducingData degree}
    {sectionFamily : ℂ → AdelicGL → ℂ} (flatSection : IsFlatSection data sectionFamily)
    (point : AdelicGL) (lower upper : ℝ) (lowerBound : -(degree : ℝ) / 2 < lower) :
    TendstoUniformlyOn
      (fun finiteSet : Finset (Flags .plane) => fun parameter =>
        ∑ flag ∈ finiteSet, eisensteinSummand sectionFamily parameter point flag)
      (fun parameter => ScalarSeries.literalSum sectionFamily parameter point)
      Filter.atTop {parameter : ℂ | lower ≤ parameter.re ∧ parameter.re ≤ upper} :=
  GlobalSeries.uniformly_on_strip flatSection point (lower : ℂ)
    (summable flatSection point (lower : ℂ) lowerBound) upper

theorem analytic {degree : ℕ} {data : InducingData degree}
    {sectionFamily : ℂ → AdelicGL → ℂ} (flatSection : IsFlatSection data sectionFamily)
    (point : AdelicGL) :
    AnalyticOnNhd ℂ (fun parameter => ScalarSeries.literalSum sectionFamily parameter point)
      {parameter : ℂ | -(degree : ℝ) / 2 < parameter.re} := by
  intro parameter rightHalfPlane
  let reference : ℂ := (((-(degree : ℝ) / 2 + parameter.re) / 2 : ℝ) : ℂ)
  have referenceBound : -(degree : ℝ) / 2 < reference.re := by
    dsimp [reference]
    change -(degree : ℝ) / 2 < parameter.re at rightHalfPlane
    linarith
  have parameterBound : reference.re < parameter.re := by
    dsimp [reference]
    change -(degree : ℝ) / 2 < parameter.re at rightHalfPlane
    linarith
  exact GlobalSeries.analytic_of_summable flatSection point reference
    (summable flatSection point reference referenceBound) parameter parameterBound

theorem meromorphic {degree : ℕ} {data : InducingData degree}
    {sectionFamily : ℂ → AdelicGL → ℂ} (flatSection : IsFlatSection data sectionFamily)
    (point : AdelicGL) :
    MeromorphicOn (fun parameter => ScalarSeries.literalSum sectionFamily parameter point)
      {parameter : ℂ | -(degree : ℝ) / 2 < parameter.re} :=
  (analytic flatSection point).meromorphicOn

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.RightHalfPlane
