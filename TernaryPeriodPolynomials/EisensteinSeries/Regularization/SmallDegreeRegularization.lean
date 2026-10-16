module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.SmallDegreeSections
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Normalized.Continuation
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.MeromorphicUniqueness

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem continuation_zero_family_order
    {family continuation : ℂ → AdelicGL → ℂ}
    (zero : family = 0) (continuation_spec : IsEisensteinContinuation family continuation)
    (matrix : AdelicGL) (point : ℂ) :
    meromorphicOrderAt (fun parameter => continuation parameter matrix) point = ⊤ := by
  apply meromorphicOrderAt_eq_top_iff.mpr
  apply meromorphic_germs_agree_of_halfplane (continuation_spec.1 matrix)
    (fun _ => analyticAt_const.meromorphicAt)
  obtain ⟨threshold, convergence⟩ := continuation_spec.2
  refine ⟨threshold, ?_⟩
  intro parameter large
  have sum := convergence parameter large matrix
  have summand_zero : eisensteinSummand family parameter matrix = 0 := by
    funext flag
    simp [eisensteinSummand, zero]
  rw [summand_zero] at sum
  exact sum.unique hasSum_zero

theorem regularization_of_small_degree
    {degree : ℕ} (small : degree < 3) {inducingData : InducingData degree}
    {family continuation : ℂ → AdelicGL → ℂ} (flat : IsFlatSection inducingData family)
    (continuation_spec : IsEisensteinContinuation family continuation) :
    ∃ repaired : ℂ → AdelicGL → ℂ,
      IsEisensteinContinuation family repaired ∧ SameOffCohomologicalPoint continuation repaired ∧
        ∀ matrix, AnalyticAt ℂ (fun parameter => repaired parameter matrix) cohomologicalPoint := by
  apply regularization_of_unitaryNormalize_order (degree := degree) continuation_spec
  intro matrix
  rw [continuation_zero_family_order (unitaryNormalize_small_degree_zero small flat.1)
    (unitaryNormalize_continuation degree continuation_spec) matrix]
  exact le_top

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
