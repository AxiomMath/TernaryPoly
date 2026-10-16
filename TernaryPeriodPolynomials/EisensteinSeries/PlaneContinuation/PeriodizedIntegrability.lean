module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.FundamentalIntegration

@[expose] public section


open MeasureTheory

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.PeriodizedIntegrability

theorem integrable {ActingGroup Space : Type*} [Group ActingGroup] [MulAction ActingGroup Space]
    [MeasurableSpace Space] [MeasurableConstSMul ActingGroup Space] [Countable ActingGroup]
    (measure : Measure Space) [SMulInvariantMeasure ActingGroup Space measure]
    (domain : Set Space) (fundamental : IsFundamentalDomain ActingGroup domain measure)
    (function : Space → ℂ) (measurable : Measurable function)
    (bound : Space → ℝ) (boundIntegrable : IntegrableOn bound domain measure)
    (summable : ∀ point, Summable (fun element : ActingGroup => ‖function (element • point)‖))
    (bounded : ∀ point, (∑' element : ActingGroup, ‖function (element • point)‖) ≤ bound point) :
    Integrable function measure := by
  refine ⟨measurable.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  calc
    _ = ∑' element : ActingGroup, ∫⁻ point in domain, ENNReal.ofReal ‖function (element • point)‖ ∂measure :=
      fundamental.lintegral_eq_tsum'' _
    _ = ∫⁻ point in domain, ∑' element : ActingGroup, ENNReal.ofReal ‖function (element • point)‖ ∂measure :=
      (lintegral_tsum (fun element => (measurable.norm.ennreal_ofReal.comp (measurable_const_smul element)).aemeasurable)).symm
    _ ≤ ∫⁻ point in domain, ENNReal.ofReal (bound point) ∂measure := by
      apply lintegral_mono
      intro point
      exact (le_of_eq (ENNReal.ofReal_tsum_of_nonneg
        (fun element : ActingGroup => norm_nonneg (function (element • point))) (summable point)).symm).trans
          (ENNReal.ofReal_le_ofReal (bounded point))
    _ < ⊤ := boundIntegrable.lintegral_lt_top

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.PeriodizedIntegrability
