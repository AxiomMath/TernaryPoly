module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Line.CompactContinuation
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Helpers

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory Filter Topology
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.UnipotentCompactDomain

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.LineCompactRegularity

theorem eventually_bounded {degree : ℕ} {data : InducingData degree}
    {extension continuation : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection data extension) (holomorphic : PlaneEisensteinHolomorphic data)
    (continues : IsEisensteinContinuation extension continuation)
    (compactRegular : LineCompactContinuation.Regular continuation) (point : AdelicGL) :
    ∃ bound : ℝ, ∀ᶠ parameter in 𝓝[≠] cohomologicalPoint,
      ∀ pair : LineCompactContinuation.Domain,
        ‖continuation parameter (lineUnipotent pair.val.1 pair.val.2 * point)‖ ≤ bound := by
  obtain ⟨family, meromorphic, equality⟩ := compactRegular point
  obtain ⟨analyticContinuation, analyticContinues, analytic⟩ := holomorphic.2 extension flat
  have pointwise (pair : WithDiscreteTopology LineCompactContinuation.Domain) :
      0 ≤ meromorphicOrderAt (fun parameter => family parameter pair) cohomologicalPoint := by
    have familyEquality : (fun parameter => family parameter pair) =
        (fun parameter => continuation parameter
          (lineUnipotent pair.ofTopology.val.1 pair.ofTopology.val.2 * point)) := by
      funext parameter
      exact equality parameter pair.ofTopology
    rw [familyEquality, meromorphicOrderAt_congr
      (TernaryPeriodPolynomials.EisensteinRegularization.Helpers.continuation_germs_agree continues analyticContinues _ cohomologicalPoint)]
    exact (analytic _).meromorphicOrderAt_nonneg
  obtain ⟨bound, bounded⟩ := BoundedMeromorphicFamily.eventually_bounded
    (meromorphic cohomologicalPoint) pointwise
  refine ⟨bound, ?_⟩
  filter_upwards [bounded] with parameter bounded
  intro pair
  rw [← equality]
  exact bounded (.toTopology ⊥ pair)

theorem average_nonnegative_order {degree : ℕ} {data : InducingData degree}
    {extension continuation : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection data extension) (holomorphic : PlaneEisensteinHolomorphic data)
    (continues : IsEisensteinContinuation extension continuation)
    (compactRegular : LineCompactContinuation.Regular continuation) (point : AdelicGL) :
    0 ≤ meromorphicOrderAt
      (fun parameter => LineConstantTerm.average (continuation parameter) point) cohomologicalPoint := by
  apply TernaryPeriodPolynomials.EisensteinRegularization.Helpers.nonnegative_order_of_eventually_bounded
    (continuation := fun parameter => LineConstantTerm.average (continuation parameter)) _ point
  intro argument
  obtain ⟨bound, bounded⟩ := eventually_bounded flat holomorphic continues compactRegular argument
  refine ⟨∫ _ : Adeles × Adeles, bound ∂LineConstantTerm.parameterMeasure, ?_⟩
  filter_upwards [bounded] with parameter bounded
  apply norm_integral_le_of_norm_le (integrable_const _)
  filter_upwards [ae_mem_domain] with pair membership
  exact bounded ⟨pair, domain_subset membership.1, domain_subset membership.2⟩

theorem average_tendsto {degree : ℕ} {data : InducingData degree}
    {extension continuation analyticContinuation : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection data extension) (holomorphic : PlaneEisensteinHolomorphic data)
    (continues : IsEisensteinContinuation extension continuation)
    (regular : LineAverageContinuation.Regular continuation)
    (compactRegular : LineCompactContinuation.Regular continuation)
    (analyticContinues : IsEisensteinContinuation extension analyticContinuation)
    (analytic : ∀ argument,
      AnalyticAt ℂ (fun parameter => analyticContinuation parameter argument) cohomologicalPoint)
    (point : AdelicGL) :
    Tendsto (fun parameter => LineConstantTerm.average (continuation parameter) point)
      (𝓝[≠] cohomologicalPoint)
      (𝓝 (LineConstantTerm.average (analyticContinuation cohomologicalPoint) point)) := by
  obtain ⟨bound, bounded⟩ := eventually_bounded flat holomorphic continues compactRegular point
  apply tendsto_integral_filter_of_dominated_convergence (fun _ => bound)
  · exact Eventually.of_forall (fun parameter => (regular.1 point parameter).aestronglyMeasurable)
  · filter_upwards [bounded] with parameter bounded
    filter_upwards [ae_mem_domain] with pair membership
    exact bounded ⟨pair, domain_subset membership.1, domain_subset membership.2⟩
  · exact integrable_const _
  · apply Eventually.of_forall
    intro pair
    have equality := TernaryPeriodPolynomials.EisensteinRegularization.Helpers.continuation_germs_agree continues analyticContinues
      (lineUnipotent pair.1 pair.2 * point) cohomologicalPoint
    exact ((analytic _).continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' equality.symm

theorem endpoint_integrable {degree : ℕ} {data : InducingData degree}
    {extension continuation analyticContinuation : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection data extension) (holomorphic : PlaneEisensteinHolomorphic data)
    (continues : IsEisensteinContinuation extension continuation)
    (regular : LineAverageContinuation.Regular continuation)
    (compactRegular : LineCompactContinuation.Regular continuation)
    (analyticContinues : IsEisensteinContinuation extension analyticContinuation)
    (analytic : ∀ argument,
      AnalyticAt ℂ (fun parameter => analyticContinuation parameter argument) cohomologicalPoint)
    (point : AdelicGL) :
    Integrable (fun pair : Adeles × Adeles =>
      analyticContinuation cohomologicalPoint (lineUnipotent pair.1 pair.2 * point))
      LineConstantTerm.parameterMeasure := by
  have pointwise (pair : Adeles × Adeles) :
      Tendsto (fun parameter => continuation parameter (lineUnipotent pair.1 pair.2 * point))
        (𝓝[≠] cohomologicalPoint)
        (𝓝 (analyticContinuation cohomologicalPoint (lineUnipotent pair.1 pair.2 * point))) := by
    have equality := TernaryPeriodPolynomials.EisensteinRegularization.Helpers.continuation_germs_agree continues analyticContinues
      (lineUnipotent pair.1 pair.2 * point) cohomologicalPoint
    exact ((analytic _).continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' equality.symm
  have measurable := aestronglyMeasurable_of_tendsto_ae (𝓝[≠] cohomologicalPoint)
    (fun parameter => (regular.1 point parameter).aestronglyMeasurable)
    (Eventually.of_forall pointwise)
  obtain ⟨bound, bounded⟩ := eventually_bounded flat holomorphic continues compactRegular point
  apply (integrable_const bound).mono' measurable
  filter_upwards [ae_mem_domain] with pair membership
  apply le_of_tendsto (pointwise pair).norm
  exact bounded.mono (fun parameter bounded =>
    bounded ⟨pair, domain_subset membership.1, domain_subset membership.2⟩)

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.LineCompactRegularity
