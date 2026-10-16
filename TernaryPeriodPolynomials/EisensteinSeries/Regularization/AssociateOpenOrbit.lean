module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.AssociateFlagCoordinates
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Radical.Unfolding

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem associate_open_unipotent_identity (rationalFirst rationalSecond : ℚ) (first second : Adeles) :
    rationalGroup ((lineUnipotent rationalFirst rationalSecond * weyl)⁻¹) * lineUnipotent first second =
      weyl⁻¹ * lineUnipotent (first - rationalAdele rationalFirst) (second - rationalAdele rationalSecond) := by
  apply Units.ext
  apply Matrix.ext
  intro row column
  fin_cases row <;> fin_cases column <;>
    simp [rationalGroup, GeneralLinearGroup.map, _root_.mul_inv_rev,
      lineUnipotent, upperUnipotent, weyl, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.map, sub_eq_add_neg, add_comm]

theorem associate_open_summand
    {degree : ℕ} {inducingData : InducingData degree}
    {family : ℂ → AdelicGL → ℂ} {parameter : ℂ}
    (induced : IsInduced inducingData .plane parameter (family parameter))
    (rational : ℚ × ℚ) (coordinates : Adeles × Adeles) (groupElement : AdelicGL) :
    eisensteinSummand family parameter (lineUnipotent coordinates.1 coordinates.2 * groupElement)
      (associateFlag (.inr rational)) =
    standardIntegrand family parameter groupElement
      (coordinates.1 - rationalAdele rational.1, coordinates.2 - rationalAdele rational.2) := by
  rw [associateFlag, associateFlagMatrix, eisensteinSummand_of_representative induced,
    ← mul_assoc, associate_open_unipotent_identity]
  rfl

theorem associate_open_integrable_integral
    {degree : ℕ} {inducingData : InducingData degree}
    {family : ℂ → AdelicGL → ℂ} {parameter : ℂ}
    (induced : IsInduced inducingData .plane parameter (family parameter))
    (groupElement : AdelicGL)
    (integrable : Integrable (standardIntegrand family parameter groupElement) radicalMeasure) :
    Integrable (fun coordinates : Adeles × Adeles => ∑' rational : ℚ × ℚ,
      eisensteinSummand family parameter (lineUnipotent coordinates.1 coordinates.2 * groupElement)
        (associateFlag (.inr rational))) planeDomainMeasure ∧
    (∫ coordinates : Adeles × Adeles, ∑' rational : ℚ × ℚ,
      eisensteinSummand family parameter (lineUnipotent coordinates.1 coordinates.2 * groupElement)
        (associateFlag (.inr rational)) ∂planeDomainMeasure) =
      ∫ coordinates, standardIntegrand family parameter groupElement coordinates ∂radicalMeasure := by
  simp_rw [associate_open_summand induced]
  exact ⟨radical_periodization_integrable _ integrable, radical_periodization_integral _ integrable⟩

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
