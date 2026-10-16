module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.ChartIntegrals

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

noncomputable def planeOpenKernel (sectionValue : AdelicGL → ℂ) (groupElement : AdelicGL) :
    Option ℚ → Adeles × Adeles → ℂ
  | none => infiniteOpenOrbitKernel sectionValue groupElement
  | some slope => finiteOpenOrbitKernel sectionValue slope groupElement

theorem planeOpenChart_estimates
    {degree : ℕ} {inducingData : InducingData degree}
    {family : ℂ → AdelicGL → ℂ} {parameter : ℂ}
    (induced : IsInduced inducingData .plane parameter (family parameter))
    (groupElement : AdelicGL)
    (kernels_integrable : ∀ slope, Integrable (planeOpenKernel (family parameter) groupElement slope)
      ((adeleMeasure.restrict additiveDomain).prod adeleMeasure)) (slope : Option ℚ) :
    Integrable (planeOpenChart family parameter groupElement slope) planeDomainMeasure ∧
      (∫ coordinates, planeOpenChart family parameter groupElement slope coordinates ∂planeDomainMeasure) = 0 ∧
      (∫⁻ coordinates, ‖planeOpenChart family parameter groupElement slope coordinates‖ₑ ∂planeDomainMeasure) ≤
        ∫⁻ coordinates, ‖planeOpenKernel (family parameter) groupElement slope coordinates‖ₑ
          ∂((adeleMeasure.restrict additiveDomain).prod adeleMeasure) := by
  cases slope with
  | none =>
    exact ⟨infinite_chart_integrable induced groupElement (kernels_integrable none),
      infinite_chart_integral_zero induced groupElement (kernels_integrable none),
      infinite_chart_norm_le induced groupElement (kernels_integrable none)⟩
  | some slope =>
    exact ⟨finite_chart_integrable induced slope groupElement (kernels_integrable (some slope)),
      finite_chart_integral_zero induced slope groupElement (kernels_integrable (some slope)),
      finite_chart_norm_le induced slope groupElement (kernels_integrable (some slope))⟩

theorem eisenstein_sum_open_charts
    {degree : ℕ} {inducingData : InducingData degree}
    {family : ℂ → AdelicGL → ℂ} {parameter sumValue : ℂ}
    (induced : IsInduced inducingData .plane parameter (family parameter))
    (groupElement : AdelicGL) (coordinates : Adeles × Adeles)
    (sum_spec : HasSum (eisensteinSummand family parameter
      (planeUnipotent coordinates.1 coordinates.2 * groupElement)) sumValue) :
    sumValue = family parameter groupElement +
      ∑' slope : Option ℚ, planeOpenChart family parameter groupElement slope coordinates := by
  let summand := eisensteinSummand family parameter
    (planeUnipotent coordinates.1 coordinates.2 * groupElement)
  have indexed_summable : Summable (fun index => summand (planeFlag index)) :=
    planeFlagEquiv.summable_iff.mpr sum_spec.summable
  have open_summable : Summable (fun index : Option ℚ × ℚ => summand (planeFlag (some index))) :=
    indexed_summable.comp_injective (Option.some_injective _)
  have closed_term : summand (planeFlag none) = family parameter groupElement := by
    dsimp only [summand, planeFlag, planeFlagMatrix]
    rw [eisensteinSummand_of_representative induced]
    simp only [inv_one, map_one, one_mul]
    exact induced.2.2.2.1 coordinates.1 coordinates.2 groupElement
  calc
    sumValue = ∑' flag, summand flag := sum_spec.tsum_eq.symm
    _ = ∑' index, summand (planeFlag index) := (planeFlagEquiv.tsum_eq summand).symm
    _ = summand (planeFlag none) + ∑' index : Option ℚ × ℚ, summand (planeFlag (some index)) :=
      summable_tsum_option _ indexed_summable
    _ = _ := by rw [closed_term, open_summable.tsum_prod]; rfl

theorem plane_constant_term_of_kernel_bounds
    {degree : ℕ} {inducingData : InducingData degree}
    {family : ℂ → AdelicGL → ℂ} {parameter : ℂ}
    (induced : IsInduced inducingData .plane parameter (family parameter))
    (groupElement : AdelicGL)
    (kernels_integrable : ∀ slope, Integrable (planeOpenKernel (family parameter) groupElement slope)
      ((adeleMeasure.restrict additiveDomain).prod adeleMeasure))
    (kernel_norm_sum_finite : (∑' slope : Option ℚ, ∫⁻ coordinates,
      ‖planeOpenKernel (family parameter) groupElement slope coordinates‖ₑ
        ∂((adeleMeasure.restrict additiveDomain).prod adeleMeasure)) ≠ ⊤)
    (sumFamily : Adeles × Adeles → ℂ)
    (actual_sums : ∀ coordinates, HasSum (eisensteinSummand family parameter
      (planeUnipotent coordinates.1 coordinates.2 * groupElement)) (sumFamily coordinates)) :
    Integrable sumFamily planeDomainMeasure ∧
      (∫ coordinates, sumFamily coordinates ∂planeDomainMeasure) = family parameter groupElement := by
  have estimates := planeOpenChart_estimates induced groupElement kernels_integrable
  have chart_measurable (slope : Option ℚ) :
      AEStronglyMeasurable (planeOpenChart family parameter groupElement slope) planeDomainMeasure :=
    (estimates slope).1.aestronglyMeasurable
  have chart_norm_sum_finite : (∑' slope : Option ℚ, ∫⁻ coordinates,
      ‖planeOpenChart family parameter groupElement slope coordinates‖ₑ ∂planeDomainMeasure) ≠ ⊤ :=
    (lt_of_le_of_lt (ENNReal.tsum_le_tsum (fun slope => (estimates slope).2.2))
      kernel_norm_sum_finite.lt_top).ne
  have open_sum_integrable := integrable_tsum_of_enorm_sum chart_measurable chart_norm_sum_finite
  have chart_integral_zero (slope : Option ℚ) :
      (∫ coordinates, planeOpenChart family parameter groupElement slope coordinates ∂planeDomainMeasure) = 0 :=
    (estimates slope).2.1
  have open_sum_integral : (∫ coordinates, ∑' slope : Option ℚ,
      planeOpenChart family parameter groupElement slope coordinates ∂planeDomainMeasure) = 0 := by
    rw [integral_tsum chart_measurable chart_norm_sum_finite]
    simp only [chart_integral_zero, tsum_zero]
  have functions_equal : sumFamily = (fun coordinates => family parameter groupElement +
      ∑' slope : Option ℚ, planeOpenChart family parameter groupElement slope coordinates) := by
    funext coordinates
    exact eisenstein_sum_open_charts induced groupElement coordinates (actual_sums coordinates)
  have constant_integrable : Integrable (fun _ : Adeles × Adeles => family parameter groupElement)
      planeDomainMeasure := integrable_const _
  rw [functions_equal]
  refine ⟨constant_integrable.add open_sum_integrable, ?_⟩
  rw [integral_add constant_integrable open_sum_integrable, open_sum_integral]
  simp

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
