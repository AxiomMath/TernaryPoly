module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.AssociateClosedOrbit
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.AssociateOpenOrbit

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

noncomputable def associateClosedTerm (family : ℂ → AdelicGL → ℂ) (parameter : ℂ)
    (groupElement : AdelicGL) (index : Option ℚ) (coordinates : Adeles × Adeles) : ℂ :=
  eisensteinSummand family parameter (lineUnipotent coordinates.1 coordinates.2 * groupElement)
    (associateFlag (.inl index))

theorem associateClosedTerm_integrable_zero
    {degree : ℕ} {inducingData : InducingData degree}
    {family : ℂ → AdelicGL → ℂ} {parameter : ℂ}
    (induced : IsInduced inducingData .plane parameter (family parameter))
    (groupElement : AdelicGL) (index : Option ℚ) :
    Integrable (associateClosedTerm family parameter groupElement index) planeDomainMeasure ∧
    (∫ coordinates, associateClosedTerm family parameter groupElement index coordinates
      ∂planeDomainMeasure) = 0 := by
  cases index with
  | none => exact associate_base_integrable_zero induced groupElement
  | some offset => exact associate_closed_integrable_zero induced offset groupElement

theorem associate_constant_term_of_bounds
    {degree : ℕ} {inducingData : InducingData degree}
    {family : ℂ → AdelicGL → ℂ} {parameter : ℂ}
    (induced : IsInduced inducingData .plane parameter (family parameter))
    (groupElement : AdelicGL)
    (standard_integrable : Integrable (standardIntegrand family parameter groupElement) radicalMeasure)
    (closed_norm_sum_finite : (∑' index : Option ℚ, ∫⁻ coordinates,
      ‖associateClosedTerm family parameter groupElement index coordinates‖ₑ ∂planeDomainMeasure) ≠ ⊤)
    (sumFamily : Adeles × Adeles → ℂ)
    (actual_sums : ∀ coordinates, HasSum (eisensteinSummand family parameter
      (lineUnipotent coordinates.1 coordinates.2 * groupElement)) (sumFamily coordinates)) :
    Integrable sumFamily planeDomainMeasure ∧
    (∫ coordinates, sumFamily coordinates ∂planeDomainMeasure) =
      ∫ coordinates, standardIntegrand family parameter groupElement coordinates ∂radicalMeasure := by
  have closed_terms := associateClosedTerm_integrable_zero induced groupElement
  have closed_measurable (index : Option ℚ) := (closed_terms index).1.aestronglyMeasurable
  have closed_integrable := integrable_tsum_of_enorm_sum closed_measurable closed_norm_sum_finite
  have closed_zero : (∫ coordinates, ∑' index : Option ℚ,
      associateClosedTerm family parameter groupElement index coordinates ∂planeDomainMeasure) = 0 := by
    rw [integral_tsum closed_measurable closed_norm_sum_finite]
    simp only [fun index => (closed_terms index).2, tsum_zero]
  have open_terms := associate_open_integrable_integral induced groupElement standard_integrable
  have functions_equal : sumFamily = (fun coordinates =>
      (∑' index : Option ℚ, associateClosedTerm family parameter groupElement index coordinates) +
        ∑' rational : ℚ × ℚ, eisensteinSummand family parameter
          (lineUnipotent coordinates.1 coordinates.2 * groupElement) (associateFlag (.inr rational))) := by
    funext coordinates
    rw [← (actual_sums coordinates).tsum_eq, associateFlag_tsum _ (actual_sums coordinates).summable]
    rfl
  rw [functions_equal]
  refine ⟨closed_integrable.add open_terms.1, ?_⟩
  rw [integral_add closed_integrable open_terms.1, closed_zero, zero_add]
  exact open_terms.2

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
