module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.RationalBruhat
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.SectionConstantTerms
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Adelic.Unfolding

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem finite_flag_unipotent_identity (slope offset : ℚ) (first second : Adeles) :
    rationalGroup ((planeUnipotent 0 offset * planeLowerShear slope * swapLastTwo)⁻¹) *
      planeUnipotent first second =
    planeLevi (binaryUnipotent first) 1 *
      lowerPlaneUnipotent 0 (second - rationalAdele offset - rationalAdele slope * first) *
        rationalGroup (swapLastTwo * planeLowerShear (-slope)) := by
  rw [_root_.mul_inv_rev, _root_.mul_inv_rev]
  have swap_inverse : swapLastTwo⁻¹ = swapLastTwo := rfl
  have shear_inverse : (planeLowerShear slope)⁻¹ = planeLowerShear (-slope) := by
    apply Units.ext
    rfl
  have unipotent_inverse : (planeUnipotent (0 : ℚ) offset)⁻¹ = planeUnipotent 0 (-offset) := by
    apply Units.ext
    simp [planeUnipotent]
  rw [swap_inverse, shear_inverse, unipotent_inverse]
  apply Units.ext
  apply Matrix.ext
  intro row column
  fin_cases row <;> fin_cases column <;>
    simp [rationalGroup, GeneralLinearGroup.map, planeUnipotent, planeLowerShear,
      swapLastTwo, planeLevi, planeBlock, binaryUnipotent, lowerPlaneUnipotent,
      Matrix.mul_apply, Fin.sum_univ_three, Matrix.map]
  all_goals ring

theorem finite_flag_eisensteinSummand
    {degree : ℕ} {inducingData : InducingData degree}
    {family : ℂ → AdelicGL → ℂ} {parameter : ℂ}
    (induced : IsInduced inducingData .plane parameter (family parameter))
    (slope offset : ℚ) (first second : Adeles) (groupElement : AdelicGL) :
    eisensteinSummand family parameter (planeUnipotent first second * groupElement)
      (QuotientGroup.mk (planeUnipotent 0 offset * planeLowerShear slope * swapLastTwo)) =
    family parameter (planeLevi (binaryUnipotent first) 1 *
      (lowerPlaneUnipotent 0 (second - rationalAdele offset - rationalAdele slope * first) *
        (rationalGroup (swapLastTwo * planeLowerShear (-slope)) * groupElement))) := by
  rw [eisensteinSummand_of_representative induced, ← mul_assoc,
    finite_flag_unipotent_identity]
  simp only [mul_assoc]

theorem open_orbit_kernel_cuspidal
    {degree : ℕ} {inducingData : InducingData degree}
    {parameter : ℂ} {sectionValue : AdelicGL → ℂ}
    (induced : IsInduced inducingData .plane parameter sectionValue)
    (slope : ℚ) (coordinate : Adeles) (groupElement : AdelicGL) :
    IntegrableOn (fun first => sectionValue (planeLevi (binaryUnipotent first) 1 *
      (lowerPlaneUnipotent 0 coordinate *
        (rationalGroup (swapLastTwo * planeLowerShear (-slope)) * groupElement))))
      additiveDomain adeleMeasure ∧
    (∫ first in additiveDomain, sectionValue (planeLevi (binaryUnipotent first) 1 *
      (lowerPlaneUnipotent 0 coordinate *
        (rationalGroup (swapLastTwo * planeLowerShear (-slope)) * groupElement))) ∂adeleMeasure) = 0 :=
  induced_binary_unipotent_cuspidal induced _

noncomputable def finiteOpenOrbitKernel (sectionValue : AdelicGL → ℂ)
    (slope : ℚ) (groupElement : AdelicGL) : Adeles × Adeles → ℂ := fun coordinates =>
  sectionValue (planeLevi (binaryUnipotent coordinates.1) 1 *
    (lowerPlaneUnipotent 0 coordinates.2 *
      (rationalGroup (swapLastTwo * planeLowerShear (-slope)) * groupElement)))

theorem finite_flag_constant_term_zero_of_integrable
    {degree : ℕ} {inducingData : InducingData degree}
    {family : ℂ → AdelicGL → ℂ} {parameter : ℂ}
    (induced : IsInduced inducingData .plane parameter (family parameter))
    (slope : ℚ) (groupElement : AdelicGL)
    (integrable : Integrable (finiteOpenOrbitKernel (family parameter) slope groupElement)
      ((adeleMeasure.restrict additiveDomain).prod adeleMeasure)) :
    (∫ first in additiveDomain, ∫ second in additiveDomain,
      ∑' offset : ℚ, eisensteinSummand family parameter (planeUnipotent first second * groupElement)
        (QuotientGroup.mk (planeUnipotent 0 offset * planeLowerShear slope * swapLastTwo))
      ∂adeleMeasure ∂adeleMeasure) = 0 := by
  calc
    _ = ∫ second, ∫ first in additiveDomain,
        finiteOpenOrbitKernel (family parameter) slope groupElement (first, second)
          ∂adeleMeasure ∂adeleMeasure := by
      simp_rw [finite_flag_eisensteinSummand induced]
      exact rational_periodization_fiber_integral
        (fun first second => finiteOpenOrbitKernel (family parameter) slope groupElement (first, second))
        (fun first => rationalAdele slope * first) integrable
    _ = 0 := by
      have inner_zero (second : Adeles) :
          (∫ first in additiveDomain,
            finiteOpenOrbitKernel (family parameter) slope groupElement (first, second) ∂adeleMeasure) = 0 :=
        (open_orbit_kernel_cuspidal induced slope second groupElement).2
      simp only [inner_zero, integral_zero]

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
