module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.ShearedPeriodization

@[expose] public section


open MeasureTheory

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.SeriesIntegrability

variable {Index Space Target : Type*} [Countable Index] [MeasurableSpace Space]
variable [NormedAddCommGroup Target] {measure : Measure Space}

omit [Countable Index] in
theorem sum_lintegral_lt_top (functions : Index → Space → Target)
    (integrable : ∀ index, Integrable (functions index) measure)
    (summable : Summable (fun index => ∫ point, ‖functions index point‖ ∂measure)) :
    (∑' index, ∫⁻ point, ‖functions index point‖ₑ ∂measure) < ⊤ := by
  simp only [← ofReal_integral_norm_eq_lintegral_enorm (integrable _)]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun index => integral_nonneg (fun point => norm_nonneg _)) summable]
  exact ENNReal.ofReal_lt_top

theorem tsum_integrable [CompleteSpace Target] (functions : Index → Space → Target)
    (integrable : ∀ index, Integrable (functions index) measure)
    (summable : Summable (fun index => ∫ point, ‖functions index point‖ ∂measure)) :
    Integrable (fun point => ∑' index, functions index point) measure := by
  refine ⟨AEStronglyMeasurable.tsum (fun index => (integrable index).aestronglyMeasurable), ?_⟩
  apply lt_of_le_of_lt (lintegral_mono (fun point => enorm_tsum_le_tsum_enorm))
  rw [lintegral_tsum (fun index => (integrable index).aestronglyMeasurable.enorm)]
  exact sum_lintegral_lt_top functions integrable summable

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.SeriesIntegrability
