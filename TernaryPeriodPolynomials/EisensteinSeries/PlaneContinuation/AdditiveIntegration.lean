module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.IntegerCube

@[expose] public section


open MeasureTheory
open scoped Pointwise

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.AdditiveIntegration

variable {ActingGroup Space Target : Type*} [AddGroup ActingGroup] [AddAction ActingGroup Space]
  [MeasurableSpace Space] [MeasurableConstVAdd ActingGroup Space]
  [NormedAddCommGroup Target]
  {measure : Measure Space} [VAddInvariantMeasure ActingGroup Space measure]

theorem integral_translate [NormedSpace ℝ Target]
    (function : Space → Target) (domain : Set Space) (element : ActingGroup) :
    ∫ point in element +ᵥ domain, function point ∂measure =
      ∫ point in domain, function (element +ᵥ point) ∂measure :=
  (measurePreserving_vadd element measure).setIntegral_image_emb
    (MeasurableEquiv.vadd element).measurableEmbedding function domain

theorem hasSum_translates [NormedSpace ℝ Target] [Countable ActingGroup] {domain : Set Space}
    (fundamental : IsAddFundamentalDomain ActingGroup domain measure)
    {function : Space → Target} (integrable : Integrable function measure) :
    HasSum (fun element : ActingGroup => ∫ point in domain, function (element +ᵥ point) ∂measure)
      (∫ point, function point ∂measure) := by
  have total : Integrable function (Measure.sum fun element : ActingGroup => measure.restrict (element +ᵥ domain)) := by
    rw [fundamental.sum_restrict]
    exact integrable
  have result := hasSum_integral_measure total
  simpa only [fundamental.sum_restrict, integral_translate] using result

theorem hasSum_norm_translates [Countable ActingGroup] {domain : Set Space}
    (fundamental : IsAddFundamentalDomain ActingGroup domain measure)
    {function : Space → Target} (integrable : Integrable function measure) :
    HasSum (fun element : ActingGroup => ∫ point in domain, ‖function (element +ᵥ point)‖ ∂measure)
      (∫ point, ‖function point‖ ∂measure) :=
  hasSum_translates fundamental integrable.norm

theorem integral_periodization [NormedSpace ℝ Target] [Countable ActingGroup] {domain : Set Space}
    (fundamental : IsAddFundamentalDomain ActingGroup domain measure)
    {function : Space → Target} (integrable : Integrable function measure) :
    (∫ point in domain, ∑' element : ActingGroup, function (element +ᵥ point) ∂measure) =
      ∫ point, function point ∂measure := by
  have translatedIntegrable : ∀ element : ActingGroup,
      IntegrableOn (fun point => function (element +ᵥ point)) domain measure :=
    fun element => ((measurePreserving_vadd element measure).integrable_comp_of_integrable integrable).integrableOn
  rw [← integral_tsum_of_summable_integral_norm translatedIntegrable
    (hasSum_norm_translates fundamental integrable).summable]
  exact (hasSum_translates fundamental integrable).tsum_eq

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.AdditiveIntegration
