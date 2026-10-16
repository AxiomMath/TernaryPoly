module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.FundamentalIntegration

@[expose] public section


open MeasureTheory
open scoped Pointwise

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.FundamentalAveraging

variable {DiscreteGroup AveragingGroup Space : Type*}
  [Group DiscreteGroup] [Group AveragingGroup] [Countable DiscreteGroup]
  [MulAction DiscreteGroup Space] [MulAction AveragingGroup Space]
  [MeasurableSpace Space] [MeasurableConstSMul DiscreteGroup Space] [MeasurableConstSMul AveragingGroup Space]
  [SMulCommClass AveragingGroup DiscreteGroup Space]
  {measure : Measure Space} [SMulInvariantMeasure DiscreteGroup Space measure] [SMulInvariantMeasure AveragingGroup Space measure]
  {domain : Set Space} (fundamental : IsFundamentalDomain DiscreteGroup domain measure)
  {Target : Type*} [NormedAddCommGroup Target] [NormedSpace ℝ Target]
  (function : Space → Target) (invariant : ∀ (element : DiscreteGroup) (point : Space), function (element • point) = function point)

include fundamental invariant

theorem integral_translate (element : AveragingGroup) :
    (∫ point in domain, function (element • point) ∂measure) = ∫ point in domain, function point ∂measure := by
  rw [← FundamentalIntegration.integral_translate]
  exact (fundamental.smul_of_comm element).setIntegral_eq fundamental invariant

omit [NormedSpace ℝ Target] in
theorem integrable_translate (integrable : IntegrableOn function domain measure) (element : AveragingGroup) :
    IntegrableOn (fun point => function (element • point)) domain measure := by
  have translated : IntegrableOn function (element • domain) measure :=
    (fundamental.integrableOn_iff (fundamental.smul_of_comm element) invariant).mp integrable
  exact ((measurePreserving_smul element measure).integrableOn_image
    (MeasurableEquiv.smul element).measurableEmbedding).mp translated

theorem integral_zero [CompleteSpace Target] {Parameter : Type*} [MeasurableSpace Parameter]
    (parameterMeasure : Measure Parameter) [IsProbabilityMeasure parameterMeasure] [SFinite measure]
    (parameter : Parameter → AveragingGroup) (integrable : IntegrableOn function domain measure)
    (measurable : AEStronglyMeasurable (fun pair : Parameter × Space => function (parameter pair.1 • pair.2))
      (parameterMeasure.prod (measure.restrict domain)))
    (averageZero : ∀ point : Space, (∫ value, function (parameter value • point) ∂parameterMeasure) = 0) :
    (∫ point in domain, function point ∂measure) = 0 := by
  have productIntegrable : Integrable (fun pair : Parameter × Space => function (parameter pair.1 • pair.2))
      (parameterMeasure.prod (measure.restrict domain)) := by
    apply (integrable_prod_iff measurable).mpr
    constructor
    · exact Filter.Eventually.of_forall (fun value => integrable_translate fundamental function invariant integrable (parameter value))
    · have normInvariant : ∀ (element : DiscreteGroup) (point : Space), ‖function (element • point)‖ = ‖function point‖ :=
        fun element point => congrArg norm (invariant element point)
      simpa only [integral_translate fundamental (fun point => ‖function point‖) normInvariant] using
        (integrable_const (μ := parameterMeasure) (∫ point in domain, ‖function point‖ ∂measure))
  have swap := integral_integral_swap (f := fun value point => function (parameter value • point)) productIntegrable
  simpa only [integral_translate fundamental function invariant, integral_const, probReal_univ, one_smul,
    averageZero, MeasureTheory.integral_zero, smul_zero] using swap

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.FundamentalAveraging
