module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Induced.FlatExtension
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.MeromorphicUniqueness

@[expose] public section


/-! Ported from the Sol reference implementation. -/

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardUniqueness

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open EisensteinRegularization.Helpers PlaneEisensteinContinuation

theorem flatSections_eq_of_endpoint {degree : ℕ} (data : InducingData degree)
    (first second : ℂ → AdelicGL → ℂ) (first_flat : IsFlatSection data first)
    (second_flat : IsFlatSection data second)
    (endpoint : first cohomologicalPoint = second cohomologicalPoint) : first = second := by
  funext parameter
  rw [InducedFlatExtension.flat_eq_extension first_flat cohomologicalPoint parameter,
    InducedFlatExtension.flat_eq_extension second_flat cohomologicalPoint parameter, endpoint]

theorem standardContinuations_eq_at_analytic_point
    {family first second : ℂ → AdelicGL → ℂ}
    (first_actual : IsStandardContinuation family first)
    (second_actual : IsStandardContinuation family second) (matrix : AdelicGL) (parameter : ℂ)
    (first_analytic : AnalyticAt ℂ (fun nearby => first nearby matrix) parameter)
    (second_analytic : AnalyticAt ℂ (fun nearby => second nearby matrix) parameter) :
    first parameter matrix = second parameter matrix := by
  have punctured := standard_continuation_germs_agree first_actual second_actual matrix parameter
  exact ((first_analytic.continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
    second_analytic.continuousAt).mp punctured).eq_of_nhds

theorem sourceFlatFamilies_eq_of_endpoint {degree : ℕ} (data : InducingData degree)
    (first second : ℂ → SourceCochain degree)
    (first_flat : ∀ vertices monomial,
      IsFlatSection data (fun parameter matrix => (first parameter vertices matrix).val.coeff monomial))
    (second_flat : ∀ vertices monomial,
      IsFlatSection data (fun parameter matrix => (second parameter vertices matrix).val.coeff monomial))
    (endpoint : first cohomologicalPoint = second cohomologicalPoint) : first = second := by
  funext parameter vertices matrix
  apply Subtype.ext
  apply MvPolynomial.ext
  intro monomial
  have scalar_endpoint :
      (fun matrix => (first cohomologicalPoint vertices matrix).val.coeff monomial) =
        (fun matrix => (second cohomologicalPoint vertices matrix).val.coeff monomial) := by
    rw [endpoint]
  have equality := flatSections_eq_of_endpoint data _ _
    (first_flat vertices monomial) (second_flat vertices monomial) scalar_endpoint
  exact congrFun (congrFun equality parameter) matrix

theorem sourceStandardEndpoints_eq {degree : ℕ}
    (family first second : ℂ → SourceCochain degree)
    (first_actual : ∀ vertices monomial, IsStandardContinuation
      (fun parameter matrix => (family parameter vertices matrix).val.coeff monomial)
      (fun parameter matrix => (first parameter vertices matrix).val.coeff monomial))
    (second_actual : ∀ vertices monomial, IsStandardContinuation
      (fun parameter matrix => (family parameter vertices matrix).val.coeff monomial)
      (fun parameter matrix => (second parameter vertices matrix).val.coeff monomial))
    (first_analytic : ∀ vertices matrix monomial, AnalyticAt ℂ
      (fun parameter => (first parameter vertices matrix).val.coeff monomial) cohomologicalPoint)
    (second_analytic : ∀ vertices matrix monomial, AnalyticAt ℂ
      (fun parameter => (second parameter vertices matrix).val.coeff monomial) cohomologicalPoint) :
    first cohomologicalPoint = second cohomologicalPoint := by
  funext vertices matrix
  apply Subtype.ext
  apply MvPolynomial.ext
  intro monomial
  exact standardContinuations_eq_at_analytic_point
    (first_actual vertices monomial) (second_actual vertices monomial) matrix cohomologicalPoint
    (first_analytic vertices matrix monomial) (second_analytic vertices matrix monomial)

theorem evaluations_unique {degree : ℕ} (data : InducingData degree) (side : Side)
    (source : SourceCochain degree) (first second : MaximalCycles degree data.chi side)
    (first_actual : Evaluates data side source first)
    (second_actual : Evaluates data side source second) : first = second := by
  apply Subtype.ext
  apply Subtype.ext
  funext vertices flag
  induction flag using Quotient.inductionOn with
  | h matrix => exact (first_actual vertices matrix).trans (second_actual vertices matrix).symm

end TernaryPeriodPolynomials.EisensteinGraph.StandardUniqueness
