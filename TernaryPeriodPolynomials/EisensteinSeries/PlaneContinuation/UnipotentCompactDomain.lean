module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Plane.ChartContinuity

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.PlaneConstantTerm

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.UnipotentCompactDomain

def closureBox : Set Adeles := Set.Icc 0 1 ×ˢ Set.range integralEmbedding

theorem closureBox_compact : IsCompact closureBox :=
  isCompact_Icc.prod (isCompact_range integralEmbedding_isOpenEmbedding.continuous)

theorem domain_subset : additiveDomain ⊆ closureBox := by
  intro value membership
  exact ⟨⟨membership.1.1, membership.1.2.le⟩, membership.2⟩

theorem ae_mem_domain : ∀ᵐ pair ∂parameterMeasure,
    pair ∈ additiveDomain ×ˢ additiveDomain := by
  rw [parameterMeasure, Measure.prod_restrict]
  exact ae_restrict_mem (RationalAdditiveDomain.domain_measurable.prod RationalAdditiveDomain.domain_measurable)

theorem continuous_integrable {Target : Type*} [NormedAddCommGroup Target]
    [NormedSpace ℝ Target] (function : Adeles × Adeles → Target) (continuous : Continuous function) :
    Integrable function parameterMeasure := by
  obtain ⟨bound, bounded⟩ := (closureBox_compact.prod closureBox_compact).exists_bound_of_continuousOn continuous.continuousOn
  apply (integrable_const (μ := parameterMeasure) bound).mono' continuous.aestronglyMeasurable
  filter_upwards [ae_mem_domain] with pair membership
  exact bounded pair ⟨domain_subset membership.1, domain_subset membership.2⟩

theorem term_integrable {degree : ℕ} {data : InducingData degree} {parameter : ℂ}
    {sectionFunction : ℂ → AdelicGL → ℂ}
    (induced : IsInduced data .plane parameter (sectionFunction parameter)) (point : AdelicGL) (flag : Flags .plane) :
    Integrable (term sectionFunction parameter point flag) parameterMeasure :=
  continuous_integrable _ (PlaneChartContinuity.term_continuous induced point flag)

theorem average_literalSum {degree : ℕ} {data : InducingData degree} {parameter : ℂ}
    {sectionFunction : ℂ → AdelicGL → ℂ}
    (induced : IsInduced data .plane parameter (sectionFunction parameter)) (point : AdelicGL)
    (summable : Summable (fun flag => ∫ pair, ‖term sectionFunction parameter point flag pair‖ ∂parameterMeasure)) :
    average (ScalarSeries.literalSum sectionFunction parameter) point = sectionFunction parameter point :=
  PlaneChartContinuity.average_literalSum induced point (term_integrable induced point) summable

theorem average_of_majorant {degree : ℕ} {data : InducingData degree} {parameter : ℂ}
    {sectionFunction : ℂ → AdelicGL → ℂ}
    (induced : IsInduced data .plane parameter (sectionFunction parameter)) (point : AdelicGL)
    (majorant : Flags .plane → ℝ) (summable : Summable majorant)
    (bounded : ∀ pair ∈ additiveDomain ×ˢ additiveDomain, ∀ flag,
      ‖term sectionFunction parameter point flag pair‖ ≤ majorant flag) :
    average (ScalarSeries.literalSum sectionFunction parameter) point = sectionFunction parameter point := by
  apply average_literalSum induced point
  apply summable.of_nonneg_of_le (fun flag => integral_nonneg (fun pair => norm_nonneg _))
  intro flag
  have boundIntegral := integral_mono_ae (term_integrable induced point flag).norm
    (integrable_const (μ := parameterMeasure) (majorant flag))
    (ae_mem_domain.mono (fun pair membership => bounded pair membership flag))
  simpa only [integral_const, probReal_univ, one_smul] using boundIntegral

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.UnipotentCompactDomain
