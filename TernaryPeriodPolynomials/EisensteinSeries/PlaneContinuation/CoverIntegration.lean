module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Siegel.Measurability

@[expose] public section


open MeasureTheory

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.CoverIntegration

variable {ActingGroup Space : Type*} [Group ActingGroup] [MulAction ActingGroup Space] [MeasurableSpace Space]
  [MeasurableConstSMul ActingGroup Space] [Countable ActingGroup]
  {measure : Measure Space} [SMulInvariantMeasure ActingGroup Space measure]

theorem lintegral_le {domain region : Set Space} (fundamental : IsFundamentalDomain ActingGroup domain measure)
    (regionMeasurable : MeasurableSet region) (cover : ∀ point, ∃ element : ActingGroup, element • point ∈ region)
    (function : Space → ENNReal) (measurable : Measurable function)
    (invariant : ∀ element : ActingGroup, ∀ point, function (element • point) = function point) :
    ∫⁻ point in domain, function point ∂measure ≤ ∫⁻ point in region, function point ∂measure := by
  have domination (point : Space) : function point ≤ ∑' element : ActingGroup, region.indicator function (element • point) := by
    obtain ⟨element, membership⟩ := cover point
    calc
      function point = region.indicator function (element • point) := by rw [Set.indicator_of_mem membership, invariant]
      _ ≤ ∑' other : ActingGroup, region.indicator function (other • point) :=
        ENNReal.le_tsum (f := fun other : ActingGroup => region.indicator function (other • point)) element
  calc
    _ ≤ ∫⁻ point in domain, ∑' element : ActingGroup, region.indicator function (element • point) ∂measure := lintegral_mono domination
    _ = ∑' element : ActingGroup, ∫⁻ point in domain, region.indicator function (element • point) ∂measure :=
      lintegral_tsum (fun element => ((measurable.indicator regionMeasurable).comp (measurable_const_smul element)).aemeasurable)
    _ = ∫⁻ point, region.indicator function point ∂measure := (fundamental.lintegral_eq_tsum'' _).symm
    _ = _ := lintegral_indicator regionMeasurable function

theorem integrableOn {domain region : Set Space} (fundamental : IsFundamentalDomain ActingGroup domain measure)
    (regionMeasurable : MeasurableSet region) (cover : ∀ point, ∃ element : ActingGroup, element • point ∈ region)
    (function : Space → ℂ) (measurable : Measurable function)
    (invariant : ∀ element : ActingGroup, ∀ point, function (element • point) = function point)
    (integrable : IntegrableOn function region measure) : IntegrableOn function domain measure := by
  refine ⟨measurable.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  exact (lintegral_le fundamental regionMeasurable cover (fun point => ENNReal.ofReal ‖function point‖)
    measurable.norm.ennreal_ofReal (fun element point => by rw [invariant])).trans_lt
      ((hasFiniteIntegral_iff_norm function).mp integrable.hasFiniteIntegral)

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.CoverIntegration
