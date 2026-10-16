module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.FlagSums
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.SeriesIntegrability

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

noncomputable def planeDomainMeasure : Measure (Adeles × Adeles) :=
  (adeleMeasure.restrict additiveDomain).prod (adeleMeasure.restrict additiveDomain)

theorem planeDomainMeasure_eq :
    planeDomainMeasure = radicalMeasure.restrict (additiveDomain ×ˢ additiveDomain) :=
  Measure.prod_restrict _ _

theorem planeDomainMeasure_univ : planeDomainMeasure Set.univ = 1 := by
  rw [planeDomainMeasure, ← Set.univ_prod_univ, Measure.prod_prod]
  simp only [Measure.restrict_apply_univ, adeleMeasure_additiveDomain, one_mul]

instance planeDomainMeasure_probability : IsProbabilityMeasure planeDomainMeasure :=
  ⟨planeDomainMeasure_univ⟩

noncomputable def planeOpenChart (family : ℂ → AdelicGL → ℂ) (parameter : ℂ)
    (groupElement : AdelicGL) (slope : Option ℚ) : Adeles × Adeles → ℂ := fun coordinates =>
  ∑' offset : ℚ, eisensteinSummand family parameter
    (planeUnipotent coordinates.1 coordinates.2 * groupElement) (planeFlag (some (slope, offset)))

theorem finite_chart_eq_periodization
    {degree : ℕ} {inducingData : InducingData degree}
    {family : ℂ → AdelicGL → ℂ} {parameter : ℂ}
    (induced : IsInduced inducingData .plane parameter (family parameter))
    (slope : ℚ) (groupElement : AdelicGL) :
    planeOpenChart family parameter groupElement (some slope) =
      (fun coordinates : Adeles × Adeles => ∑' offset : ℚ,
        finiteOpenOrbitKernel (family parameter) slope groupElement
          (coordinates.1, coordinates.2 - rationalAdele offset - rationalAdele slope * coordinates.1)) := by
  funext coordinates
  apply tsum_congr
  intro offset
  exact finite_flag_eisensteinSummand induced slope offset coordinates.1 coordinates.2 groupElement

theorem infinite_chart_eq_periodization
    {degree : ℕ} {inducingData : InducingData degree}
    {family : ℂ → AdelicGL → ℂ} {parameter : ℂ}
    (induced : IsInduced inducingData .plane parameter (family parameter))
    (groupElement : AdelicGL) :
    planeOpenChart family parameter groupElement none =
      (fun coordinates : Adeles × Adeles => ∑' offset : ℚ,
        infiniteOpenOrbitKernel (family parameter) groupElement
          (coordinates.2, coordinates.1 - rationalAdele offset)) := by
  funext coordinates
  apply tsum_congr
  intro offset
  exact infinite_flag_eisensteinSummand induced offset coordinates.1 coordinates.2 groupElement

theorem finite_chart_integrable
    {degree : ℕ} {inducingData : InducingData degree}
    {family : ℂ → AdelicGL → ℂ} {parameter : ℂ}
    (induced : IsInduced inducingData .plane parameter (family parameter))
    (slope : ℚ) (groupElement : AdelicGL)
    (kernel_integrable : Integrable (finiteOpenOrbitKernel (family parameter) slope groupElement)
      ((adeleMeasure.restrict additiveDomain).prod adeleMeasure)) :
    Integrable (planeOpenChart family parameter groupElement (some slope)) planeDomainMeasure := by
  have period_integrable := rational_fiber_periodization_integrable
    (adeleMeasure.restrict additiveDomain) (finiteOpenOrbitKernel (family parameter) slope groupElement)
    (fun first => rationalAdele slope * first) (continuous_const.mul continuous_id).measurable
    kernel_integrable
  rw [finite_chart_eq_periodization induced]
  exact period_integrable

theorem finite_chart_integral_zero
    {degree : ℕ} {inducingData : InducingData degree}
    {family : ℂ → AdelicGL → ℂ} {parameter : ℂ}
    (induced : IsInduced inducingData .plane parameter (family parameter))
    (slope : ℚ) (groupElement : AdelicGL)
    (kernel_integrable : Integrable (finiteOpenOrbitKernel (family parameter) slope groupElement)
      ((adeleMeasure.restrict additiveDomain).prod adeleMeasure)) :
    (∫ coordinates, planeOpenChart family parameter groupElement (some slope) coordinates
      ∂planeDomainMeasure) = 0 := by
  rw [planeDomainMeasure, integral_prod _ (finite_chart_integrable induced slope groupElement kernel_integrable)]
  exact finite_flag_constant_term_zero_of_integrable induced slope groupElement kernel_integrable

theorem infinite_chart_integrable
    {degree : ℕ} {inducingData : InducingData degree}
    {family : ℂ → AdelicGL → ℂ} {parameter : ℂ}
    (induced : IsInduced inducingData .plane parameter (family parameter))
    (groupElement : AdelicGL)
    (kernel_integrable : Integrable (infiniteOpenOrbitKernel (family parameter) groupElement)
      ((adeleMeasure.restrict additiveDomain).prod adeleMeasure)) :
    Integrable (planeOpenChart family parameter groupElement none) planeDomainMeasure := by
  have period_integrable := rational_fiber_periodization_integrable
    (adeleMeasure.restrict additiveDomain) (infiniteOpenOrbitKernel (family parameter) groupElement)
    (fun _ => 0) measurable_const kernel_integrable
  have swapped_integrable := period_integrable.swap
  rw [infinite_chart_eq_periodization induced]
  simpa only [Function.comp_def, Prod.swap, sub_zero, planeDomainMeasure] using swapped_integrable

theorem infinite_chart_integral_zero
    {degree : ℕ} {inducingData : InducingData degree}
    {family : ℂ → AdelicGL → ℂ} {parameter : ℂ}
    (induced : IsInduced inducingData .plane parameter (family parameter))
    (groupElement : AdelicGL)
    (kernel_integrable : Integrable (infiniteOpenOrbitKernel (family parameter) groupElement)
      ((adeleMeasure.restrict additiveDomain).prod adeleMeasure)) :
    (∫ coordinates, planeOpenChart family parameter groupElement none coordinates ∂planeDomainMeasure) = 0 := by
  rw [planeDomainMeasure,
    integral_prod_symm _ (infinite_chart_integrable induced groupElement kernel_integrable)]
  exact infinite_flag_constant_term_zero_of_integrable induced groupElement kernel_integrable

theorem finite_chart_norm_le
    {degree : ℕ} {inducingData : InducingData degree}
    {family : ℂ → AdelicGL → ℂ} {parameter : ℂ}
    (induced : IsInduced inducingData .plane parameter (family parameter))
    (slope : ℚ) (groupElement : AdelicGL)
    (kernel_integrable : Integrable (finiteOpenOrbitKernel (family parameter) slope groupElement)
      ((adeleMeasure.restrict additiveDomain).prod adeleMeasure)) :
    (∫⁻ coordinates, ‖planeOpenChart family parameter groupElement (some slope) coordinates‖ₑ
      ∂planeDomainMeasure) ≤
      ∫⁻ coordinates, ‖finiteOpenOrbitKernel (family parameter) slope groupElement coordinates‖ₑ
        ∂((adeleMeasure.restrict additiveDomain).prod adeleMeasure) := by
  rw [finite_chart_eq_periodization induced]
  exact rational_fiber_periodization_norm_le (adeleMeasure.restrict additiveDomain)
    (finiteOpenOrbitKernel (family parameter) slope groupElement)
    (fun first => rationalAdele slope * first) (continuous_const.mul continuous_id).measurable
    kernel_integrable

theorem infinite_chart_norm_le
    {degree : ℕ} {inducingData : InducingData degree}
    {family : ℂ → AdelicGL → ℂ} {parameter : ℂ}
    (induced : IsInduced inducingData .plane parameter (family parameter))
    (groupElement : AdelicGL)
    (kernel_integrable : Integrable (infiniteOpenOrbitKernel (family parameter) groupElement)
      ((adeleMeasure.restrict additiveDomain).prod adeleMeasure)) :
    (∫⁻ coordinates, ‖planeOpenChart family parameter groupElement none coordinates‖ₑ
      ∂planeDomainMeasure) ≤
      ∫⁻ coordinates, ‖infiniteOpenOrbitKernel (family parameter) groupElement coordinates‖ₑ
        ∂((adeleMeasure.restrict additiveDomain).prod adeleMeasure) := by
  rw [infinite_chart_eq_periodization induced]
  have swap_integral := lintegral_prod_swap
    (μ := adeleMeasure.restrict additiveDomain) (ν := adeleMeasure.restrict additiveDomain)
    (fun coordinates : Adeles × Adeles => ‖∑' offset : ℚ,
      infiniteOpenOrbitKernel (family parameter) groupElement
        (coordinates.1, coordinates.2 - rationalAdele offset)‖ₑ)
  change (∫⁻ coordinates : Adeles × Adeles, ‖∑' offset : ℚ,
    infiniteOpenOrbitKernel (family parameter) groupElement
      (coordinates.2, coordinates.1 - rationalAdele offset)‖ₑ
      ∂((adeleMeasure.restrict additiveDomain).prod (adeleMeasure.restrict additiveDomain))) ≤ _
  simp only [Prod.swap] at swap_integral
  rw [swap_integral]
  simpa only [sub_zero] using rational_fiber_periodization_norm_le
    (adeleMeasure.restrict additiveDomain) (infiniteOpenOrbitKernel (family parameter) groupElement)
    (fun _ => 0) measurable_const kernel_integrable

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
