module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Binary.Periodicity
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.PeriodicShear
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.ChartIntegrals

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem induced_binary_unipotent_shear
    {degree : ℕ} {inducingData : InducingData degree}
    {parameter : ℂ} {sectionValue : AdelicGL → ℂ}
    (induced : IsInduced inducingData .plane parameter sectionValue)
    (groupElement : AdelicGL) (shift : Adeles → Adeles) (shift_measurable : Measurable shift) :
    Integrable (fun coordinates : Adeles × Adeles =>
      sectionValue (planeLevi (binaryUnipotent (coordinates.2 - shift coordinates.1)) 1 * groupElement))
        planeDomainMeasure ∧
    (∫ coordinates : Adeles × Adeles,
      sectionValue (planeLevi (binaryUnipotent (coordinates.2 - shift coordinates.1)) 1 * groupElement)
        ∂planeDomainMeasure) = 0 := by
  have cusp := induced_binary_unipotent_cuspidal induced groupElement
  have periodic := induced_binary_unipotent_periodic induced groupElement
  refine ⟨rational_periodic_shear_integrable _ periodic cusp.1
    (adeleMeasure.restrict additiveDomain) shift shift_measurable, ?_⟩
  rw [planeDomainMeasure, rational_periodic_shear_integral _ periodic cusp.1]
  · exact cusp.2
  · exact shift_measurable

theorem lineUnipotent_plane_binary {R : Type*} [CommRing R] (first second : R) :
    lineUnipotent first second = planeUnipotent second 0 * planeLevi (binaryUnipotent first) 1 := by
  apply Units.ext
  apply Matrix.ext
  intro row column
  fin_cases row <;> fin_cases column <;>
    simp [lineUnipotent, upperUnipotent, planeUnipotent, planeLevi, planeBlock,
      binaryUnipotent, Matrix.mul_apply, Fin.sum_univ_three]

theorem associate_base_summand
    {degree : ℕ} {inducingData : InducingData degree}
    {family : ℂ → AdelicGL → ℂ} {parameter : ℂ}
    (induced : IsInduced inducingData .plane parameter (family parameter))
    (first second : Adeles) (groupElement : AdelicGL) :
    eisensteinSummand family parameter (lineUnipotent first second * groupElement) (planeFlag none) =
      family parameter (planeLevi (binaryUnipotent first) 1 * groupElement) := by
  rw [planeFlag, planeFlagMatrix, eisensteinSummand_of_representative induced]
  simp only [inv_one, map_one, one_mul, lineUnipotent_plane_binary, mul_assoc,
    induced.2.2.2.1]

theorem associate_base_integrable_zero
    {degree : ℕ} {inducingData : InducingData degree}
    {family : ℂ → AdelicGL → ℂ} {parameter : ℂ}
    (induced : IsInduced inducingData .plane parameter (family parameter))
    (groupElement : AdelicGL) :
    Integrable (fun coordinates : Adeles × Adeles =>
      eisensteinSummand family parameter (lineUnipotent coordinates.1 coordinates.2 * groupElement)
        (planeFlag none)) planeDomainMeasure ∧
    (∫ coordinates : Adeles × Adeles,
      eisensteinSummand family parameter (lineUnipotent coordinates.1 coordinates.2 * groupElement)
        (planeFlag none) ∂planeDomainMeasure) = 0 := by
  simp_rw [associate_base_summand induced]
  have second := induced_binary_unipotent_shear induced groupElement (fun _ => 0) measurable_const
  simp only [sub_zero] at second
  refine ⟨?_, ?_⟩
  · simpa only [planeDomainMeasure, Function.comp_def, Prod.swap] using second.1.swap
  · rw [planeDomainMeasure, integral_prod]
    · simpa using (induced_binary_unipotent_cuspidal induced groupElement).2
    · simpa only [planeDomainMeasure, Function.comp_def, Prod.swap] using second.1.swap

theorem associate_closed_unipotent_identity (offset : ℚ) (first second : Adeles) :
    rationalGroup ((planeUnipotent 0 offset * swapLastTwo)⁻¹) * lineUnipotent first second =
      planeUnipotent first 0 * planeLevi (binaryUnipotent (second + rationalAdele offset * first)) 1 *
        rationalGroup ((planeUnipotent 0 offset * swapLastTwo)⁻¹) := by
  apply Units.ext
  apply Matrix.ext
  intro row column
  fin_cases row <;> fin_cases column <;>
    simp [rationalGroup, GeneralLinearGroup.map, _root_.mul_inv_rev,
      planeUnipotent, swapLastTwo, lineUnipotent, upperUnipotent, planeLevi, planeBlock,
      binaryUnipotent, Matrix.mul_apply, Fin.sum_univ_three, Matrix.map]
  all_goals ring

theorem associate_closed_summand
    {degree : ℕ} {inducingData : InducingData degree}
    {family : ℂ → AdelicGL → ℂ} {parameter : ℂ}
    (induced : IsInduced inducingData .plane parameter (family parameter))
    (offset : ℚ) (first second : Adeles) (groupElement : AdelicGL) :
    eisensteinSummand family parameter (lineUnipotent first second * groupElement)
      (QuotientGroup.mk (planeUnipotent 0 offset * swapLastTwo)) =
    family parameter (planeLevi (binaryUnipotent (second + rationalAdele offset * first)) 1 *
      (rationalGroup ((planeUnipotent 0 offset * swapLastTwo)⁻¹) * groupElement)) := by
  rw [eisensteinSummand_of_representative induced, ← mul_assoc, associate_closed_unipotent_identity]
  simp only [mul_assoc, induced.2.2.2.1]

theorem associate_closed_integrable_zero
    {degree : ℕ} {inducingData : InducingData degree}
    {family : ℂ → AdelicGL → ℂ} {parameter : ℂ}
    (induced : IsInduced inducingData .plane parameter (family parameter))
    (offset : ℚ) (groupElement : AdelicGL) :
    Integrable (fun coordinates : Adeles × Adeles =>
      eisensteinSummand family parameter (lineUnipotent coordinates.1 coordinates.2 * groupElement)
        (QuotientGroup.mk (planeUnipotent 0 offset * swapLastTwo))) planeDomainMeasure ∧
    (∫ coordinates : Adeles × Adeles,
      eisensteinSummand family parameter (lineUnipotent coordinates.1 coordinates.2 * groupElement)
        (QuotientGroup.mk (planeUnipotent 0 offset * swapLastTwo)) ∂planeDomainMeasure) = 0 := by
  simp_rw [associate_closed_summand induced]
  simpa only [sub_neg_eq_add] using induced_binary_unipotent_shear induced
    (rationalGroup ((planeUnipotent 0 offset * swapLastTwo)⁻¹) * groupElement)
    (fun first => -(rationalAdele offset * first))
    (continuous_const.mul continuous_id).neg.measurable

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
