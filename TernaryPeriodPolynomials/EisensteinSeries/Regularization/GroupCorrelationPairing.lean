module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.BoundedGroupAverages

@[expose] public section


open MeasureTheory

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

theorem rightGroupAverage_correlation_pairing
    {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G]
    (measure : Measure G) [SFinite measure] (domainMeasure : Measure G) [IsFiniteMeasure domainMeasure]
    {function kernel : G → ℂ} (measurable : Measurable function)
    (kernel_integrable : Integrable kernel measure) {bound : ℝ} (nonnegative : 0 ≤ bound)
    (bounded : ∀ point, ‖function point‖ ≤ bound) :
    (∫ point, function point * star (rightGroupAverage measure function kernel point) ∂domainMeasure) =
      ∫ shift, (∫ point, function point * star (function (point * shift)) ∂domainMeasure) * star (kernel shift) ∂measure := by
  have joint_integrable : Integrable (fun pair : G × G =>
      function pair.1 * star (function (pair.1 * pair.2) * kernel pair.2)) (domainMeasure.prod measure) := by
    apply ((kernel_integrable.norm.const_mul (bound * bound)).comp_snd domainMeasure).mono'
      ((measurable.comp measurable_fst).aestronglyMeasurable.mul
        (((measurable.comp (measurable_fst.mul measurable_snd)).aestronglyMeasurable.mul
          (kernel_integrable.aestronglyMeasurable.comp_snd (μ := domainMeasure))).star))
    apply Filter.Eventually.of_forall
    intro pair
    change ‖function pair.1 * star (function (pair.1 * pair.2) * kernel pair.2)‖ ≤ _
    simp only [norm_mul, norm_star]
    calc
      _ ≤ bound * (bound * ‖kernel pair.2‖) := by
        gcongr
        · exact bounded _
        · exact bounded _
      _ = _ := by ring
  calc
    _ = ∫ point, ∫ shift, function point * star (function (point * shift) * kernel shift) ∂measure ∂domainMeasure := by
      congr 1
      funext point
      change function point * (starRingEnd ℂ) (∫ shift, function (point * shift) * kernel shift ∂measure) = _
      rw [← integral_conj, integral_const_mul]
      rfl
    _ = ∫ shift, ∫ point, function point * star (function (point * shift) * kernel shift) ∂domainMeasure ∂measure :=
      integral_integral_swap joint_integrable
    _ = _ := by
      congr 1
      funext shift
      simp only [star_mul, mul_comm (star (kernel shift)), ← mul_assoc, integral_mul_const]

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
