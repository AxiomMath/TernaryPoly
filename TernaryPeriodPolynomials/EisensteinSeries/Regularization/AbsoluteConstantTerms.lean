module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Radical.Continuity
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Plane.ConstantTerm
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.AssociateConstantTerm

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem plane_kernel_norm_eq
    {degree : ℕ} {inducingData : InducingData degree}
    {family : ℂ → AdelicGL → ℂ} {parameter : ℂ}
    (induced : IsInduced inducingData .plane parameter (family parameter))
    (groupElement : AdelicGL) (slope : Option ℚ) :
    (∫⁻ coordinates, ‖planeOpenKernel (family parameter) groupElement slope coordinates‖ₑ
      ∂((adeleMeasure.restrict additiveDomain).prod adeleMeasure)) =
      ∑' offset : ℚ, ∫⁻ coordinates : Adeles × Adeles,
        ‖eisensteinSummand family parameter (planeUnipotent coordinates.1 coordinates.2 * groupElement)
          (planeFlag (some (slope, offset)))‖ₑ ∂planeDomainMeasure := by
  cases slope with
  | some slope =>
    have unfolding := rational_fiber_norm_sum_of_measurable
      (adeleMeasure.restrict additiveDomain) (finiteOpenOrbitKernel (family parameter) slope groupElement)
      (fun first => rationalAdele slope * first) (continuous_const.mul continuous_id).measurable
      (finiteOpenOrbitKernel_continuous induced slope groupElement).aestronglyMeasurable
    change _ = ∑' offset : ℚ, ∫⁻ coordinates : Adeles × Adeles,
      ‖eisensteinSummand family parameter (planeUnipotent coordinates.1 coordinates.2 * groupElement)
        (QuotientGroup.mk (planeUnipotent 0 offset * planeLowerShear slope * GeneralEisenstein.swapLastTwo))‖ₑ
        ∂planeDomainMeasure
    simp_rw [finite_flag_eisensteinSummand induced]
    exact unfolding.symm
  | none =>
    have unfolding := rational_fiber_norm_sum_of_measurable
      (adeleMeasure.restrict additiveDomain) (infiniteOpenOrbitKernel (family parameter) groupElement)
      (fun _ => 0) measurable_const
      (infiniteOpenOrbitKernel_continuous induced groupElement).aestronglyMeasurable
    calc
      _ = ∑' offset : ℚ, ∫⁻ coordinates : Adeles × Adeles,
          ‖infiniteOpenOrbitKernel (family parameter) groupElement
            (coordinates.1, coordinates.2 - rationalAdele offset)‖ₑ ∂planeDomainMeasure := by
        simpa only [planeOpenKernel, sub_zero, planeDomainMeasure] using unfolding.symm
      _ = _ := by
        apply tsum_congr
        intro offset
        simp_rw [infinite_flag_eisensteinSummand induced]
        simpa only [Prod.swap, infiniteOpenOrbitKernel, planeDomainMeasure] using
          (lintegral_prod_swap (μ := adeleMeasure.restrict additiveDomain)
            (ν := adeleMeasure.restrict additiveDomain)
            (fun coordinates : Adeles × Adeles =>
              ‖infiniteOpenOrbitKernel (family parameter) groupElement
                (coordinates.1, coordinates.2 - rationalAdele offset)‖ₑ)).symm

theorem plane_kernel_norm_sum_le
    {degree : ℕ} {inducingData : InducingData degree}
    {family : ℂ → AdelicGL → ℂ} {parameter : ℂ}
    (induced : IsInduced inducingData .plane parameter (family parameter)) (groupElement : AdelicGL) :
    (∑' slope : Option ℚ, ∫⁻ coordinates,
      ‖planeOpenKernel (family parameter) groupElement slope coordinates‖ₑ
        ∂((adeleMeasure.restrict additiveDomain).prod adeleMeasure)) ≤
    ∑' flag : Flags .plane, ∫⁻ coordinates : Adeles × Adeles,
      ‖eisensteinSummand family parameter (planeUnipotent coordinates.1 coordinates.2 * groupElement) flag‖ₑ
        ∂planeDomainMeasure := by
  simp_rw [plane_kernel_norm_eq induced groupElement]
  rw [← ENNReal.tsum_prod]
  exact le_trans (le_of_eq (by rfl)) <| ENNReal.tsum_comp_le_tsum_of_injective
    (planeFlag_injective.comp (Option.some_injective _)) _

theorem plane_constant_term_of_absolute_integrability
    {degree : ℕ} {inducingData : InducingData degree}
    {family : ℂ → AdelicGL → ℂ} {parameter : ℂ}
    (induced : IsInduced inducingData .plane parameter (family parameter)) (groupElement : AdelicGL)
    (absolute_integrability : (∑' flag : Flags .plane, ∫⁻ coordinates : Adeles × Adeles,
      ‖eisensteinSummand family parameter (planeUnipotent coordinates.1 coordinates.2 * groupElement) flag‖ₑ
        ∂planeDomainMeasure) ≠ ⊤)
    (sumFamily : Adeles × Adeles → ℂ)
    (actual_sums : ∀ coordinates, HasSum (eisensteinSummand family parameter
      (planeUnipotent coordinates.1 coordinates.2 * groupElement)) (sumFamily coordinates)) :
    Integrable sumFamily planeDomainMeasure ∧
      (∫ coordinates, sumFamily coordinates ∂planeDomainMeasure) = family parameter groupElement := by
  have norm_sum_lt := lt_of_le_of_lt (plane_kernel_norm_sum_le induced groupElement)
    absolute_integrability.lt_top
  apply plane_constant_term_of_kernel_bounds induced groupElement _ norm_sum_lt.ne sumFamily actual_sums
  intro slope
  have continuous : Continuous (planeOpenKernel (family parameter) groupElement slope) := by
    cases slope with
    | none => exact infiniteOpenOrbitKernel_continuous induced groupElement
    | some slope => exact finiteOpenOrbitKernel_continuous induced slope groupElement
  refine ⟨continuous.aestronglyMeasurable, ?_⟩
  exact (ENNReal.le_tsum slope).trans_lt norm_sum_lt

theorem standard_norm_le_line_summands
    {degree : ℕ} {inducingData : InducingData degree}
    {family : ℂ → AdelicGL → ℂ} {parameter : ℂ}
    (induced : IsInduced inducingData .plane parameter (family parameter)) (groupElement : AdelicGL) :
    (∫⁻ coordinates, ‖standardIntegrand family parameter groupElement coordinates‖ₑ ∂radicalMeasure) ≤
      ∑' flag : Flags .plane, ∫⁻ coordinates : Adeles × Adeles,
        ‖eisensteinSummand family parameter (lineUnipotent coordinates.1 coordinates.2 * groupElement) flag‖ₑ
          ∂planeDomainMeasure := by
  rw [radical_lintegral_eq_rational_tsum]
  simp_rw [← associate_open_summand induced]
  exact le_trans (le_of_eq (by rfl)) <| ENNReal.tsum_comp_le_tsum_of_injective
    (associateFlag_injective.comp Sum.inr_injective) _

theorem associate_constant_term_of_absolute_integrability
    {degree : ℕ} {inducingData : InducingData degree}
    {family : ℂ → AdelicGL → ℂ} {parameter : ℂ}
    (induced : IsInduced inducingData .plane parameter (family parameter)) (groupElement : AdelicGL)
    (absolute_integrability : (∑' flag : Flags .plane, ∫⁻ coordinates : Adeles × Adeles,
      ‖eisensteinSummand family parameter (lineUnipotent coordinates.1 coordinates.2 * groupElement) flag‖ₑ
        ∂planeDomainMeasure) ≠ ⊤)
    (sumFamily : Adeles × Adeles → ℂ)
    (actual_sums : ∀ coordinates, HasSum (eisensteinSummand family parameter
      (lineUnipotent coordinates.1 coordinates.2 * groupElement)) (sumFamily coordinates)) :
    Integrable sumFamily planeDomainMeasure ∧
    (∫ coordinates, sumFamily coordinates ∂planeDomainMeasure) =
      ∫ coordinates, standardIntegrand family parameter groupElement coordinates ∂radicalMeasure := by
  have standard_integrable : Integrable (standardIntegrand family parameter groupElement) radicalMeasure :=
    ⟨(standardIntegrand_continuous induced groupElement).aestronglyMeasurable,
      lt_of_le_of_lt (standard_norm_le_line_summands induced groupElement) absolute_integrability.lt_top⟩
  have closed_bound : (∑' index : Option ℚ, ∫⁻ coordinates,
      ‖associateClosedTerm family parameter groupElement index coordinates‖ₑ ∂planeDomainMeasure) ≤
      ∑' flag : Flags .plane, ∫⁻ coordinates : Adeles × Adeles,
        ‖eisensteinSummand family parameter (lineUnipotent coordinates.1 coordinates.2 * groupElement) flag‖ₑ
          ∂planeDomainMeasure :=
    le_trans (le_of_eq (by rfl)) <|
      ENNReal.tsum_comp_le_tsum_of_injective (associateFlag_injective.comp Sum.inl_injective) _
  exact associate_constant_term_of_bounds induced groupElement standard_integrable
    (lt_of_le_of_lt closed_bound absolute_integrability.lt_top).ne sumFamily actual_sums

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
