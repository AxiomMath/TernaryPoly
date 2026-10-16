module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Binary.FundamentalDomain

@[expose] public section


open MeasureTheory
open scoped Pointwise

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.FundamentalIntegration

variable {ActingGroup Space Target : Type*} [Group ActingGroup] [MulAction ActingGroup Space]
  [MeasurableSpace Space] [MeasurableConstSMul ActingGroup Space]
  [NormedAddCommGroup Target]
  {measure : Measure Space} [SMulInvariantMeasure ActingGroup Space measure]

theorem integral_translate [NormedSpace ℝ Target]
    (function : Space → Target) (domain : Set Space) (element : ActingGroup) :
    ∫ point in element • domain, function point ∂measure =
      ∫ point in domain, function (element • point) ∂measure :=
  (measurePreserving_smul element measure).setIntegral_image_emb
    (MeasurableEquiv.smul element).measurableEmbedding function domain

theorem hasSum_translates [NormedSpace ℝ Target] [Countable ActingGroup] {domain : Set Space}
    (fundamental : IsFundamentalDomain ActingGroup domain measure)
    {function : Space → Target} (integrable : Integrable function measure) :
    HasSum (fun element : ActingGroup => ∫ point in domain, function (element • point) ∂measure)
      (∫ point, function point ∂measure) := by
  have total : Integrable function (Measure.sum fun element : ActingGroup => measure.restrict (element • domain)) := by
    rw [fundamental.sum_restrict]
    exact integrable
  have result := hasSum_integral_measure total
  simpa only [fundamental.sum_restrict, integral_translate] using result

theorem hasSum_norm_translates [Countable ActingGroup] {domain : Set Space}
    (fundamental : IsFundamentalDomain ActingGroup domain measure)
    {function : Space → Target} (integrable : Integrable function measure) :
    HasSum (fun element : ActingGroup => ∫ point in domain, ‖function (element • point)‖ ∂measure)
      (∫ point, ‖function point‖ ∂measure) :=
  hasSum_translates fundamental integrable.norm

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.FundamentalIntegration
