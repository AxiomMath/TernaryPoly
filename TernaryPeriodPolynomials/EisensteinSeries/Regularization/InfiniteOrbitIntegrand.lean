module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.OpenOrbitIntegrand
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.FlagCoordinates

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem infinite_flag_unipotent_identity (offset : ℚ) (first second : Adeles) :
    rationalGroup ((planeUnipotent offset 0 * swapFirstTwo * swapLastTwo)⁻¹) *
      planeUnipotent first second =
    planeLevi (binaryUnipotent second) 1 * lowerPlaneUnipotent 0 (first - rationalAdele offset) *
      rationalGroup (swapLastTwo * swapFirstTwo) := by
  rw [_root_.mul_inv_rev, _root_.mul_inv_rev]
  have swap_last_inverse : swapLastTwo⁻¹ = swapLastTwo := rfl
  have swap_first_inverse : swapFirstTwo⁻¹ = swapFirstTwo := rfl
  have unipotent_inverse : (planeUnipotent offset (0 : ℚ))⁻¹ = planeUnipotent (-offset) 0 := by
    apply Units.ext
    simp [planeUnipotent]
  rw [swap_last_inverse, swap_first_inverse, unipotent_inverse]
  apply Units.ext
  apply Matrix.ext
  intro row column
  fin_cases row <;> fin_cases column <;>
    simp [rationalGroup, GeneralLinearGroup.map, planeUnipotent, swapFirstTwo,
      swapLastTwo, planeLevi, planeBlock, binaryUnipotent, lowerPlaneUnipotent,
      Matrix.mul_apply, Fin.sum_univ_three, Matrix.map, sub_eq_add_neg]

theorem infinite_flag_eisensteinSummand
    {degree : ℕ} {inducingData : InducingData degree}
    {family : ℂ → AdelicGL → ℂ} {parameter : ℂ}
    (induced : IsInduced inducingData .plane parameter (family parameter))
    (offset : ℚ) (first second : Adeles) (groupElement : AdelicGL) :
    eisensteinSummand family parameter (planeUnipotent first second * groupElement)
      (planeFlag (some (none, offset))) =
    family parameter (planeLevi (binaryUnipotent second) 1 *
      (lowerPlaneUnipotent 0 (first - rationalAdele offset) *
        (rationalGroup (swapLastTwo * swapFirstTwo) * groupElement))) := by
  rw [planeFlag, planeFlagMatrix, eisensteinSummand_of_representative induced,
    ← mul_assoc, infinite_flag_unipotent_identity]
  simp only [mul_assoc]

noncomputable def infiniteOpenOrbitKernel (sectionValue : AdelicGL → ℂ)
    (groupElement : AdelicGL) : Adeles × Adeles → ℂ := fun coordinates =>
  sectionValue (planeLevi (binaryUnipotent coordinates.1) 1 *
    (lowerPlaneUnipotent 0 coordinates.2 *
      (rationalGroup (swapLastTwo * swapFirstTwo) * groupElement)))

theorem infinite_flag_constant_term_zero_of_integrable
    {degree : ℕ} {inducingData : InducingData degree}
    {family : ℂ → AdelicGL → ℂ} {parameter : ℂ}
    (induced : IsInduced inducingData .plane parameter (family parameter))
    (groupElement : AdelicGL)
    (integrable : Integrable (infiniteOpenOrbitKernel (family parameter) groupElement)
      ((adeleMeasure.restrict additiveDomain).prod adeleMeasure)) :
    (∫ second in additiveDomain, ∫ first in additiveDomain,
      ∑' offset : ℚ, eisensteinSummand family parameter (planeUnipotent first second * groupElement)
        (planeFlag (some (none, offset))) ∂adeleMeasure ∂adeleMeasure) = 0 := by
  calc
    _ = ∫ coordinate, ∫ second in additiveDomain,
        infiniteOpenOrbitKernel (family parameter) groupElement (second, coordinate)
          ∂adeleMeasure ∂adeleMeasure := by
      simp_rw [infinite_flag_eisensteinSummand induced]
      simpa only [sub_zero, infiniteOpenOrbitKernel] using rational_periodization_fiber_integral
        (fun second coordinate => infiniteOpenOrbitKernel (family parameter) groupElement (second, coordinate))
        (fun _ => 0) integrable
    _ = 0 := by
      have inner_zero (coordinate : Adeles) :
          (∫ second in additiveDomain,
            infiniteOpenOrbitKernel (family parameter) groupElement (second, coordinate) ∂adeleMeasure) = 0 := by
        unfold infiniteOpenOrbitKernel
        exact (induced_binary_unipotent_cuspidal induced
          (lowerPlaneUnipotent 0 coordinate *
            (rationalGroup (swapLastTwo * swapFirstTwo) * groupElement))).2
      simp only [inner_zero, integral_zero]

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
