module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Normalized.Symmetries

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem det_binaryUnipotent {R : Type*} [CommRing R] (coordinate : R) :
    GeneralLinearGroup.det (binaryUnipotent coordinate) = 1 := by
  apply Units.ext
  simp [GeneralLinearGroup.det, binaryUnipotent, Matrix.det_fin_two]

theorem induced_binary_unipotent_cuspidal
    {degree : ℕ} {inducingData : InducingData degree}
    {parameter : ℂ} {sectionValue : AdelicGL → ℂ}
    (induced : IsInduced inducingData .plane parameter sectionValue)
    (groupElement : AdelicGL) :
    IntegrableOn (fun coordinate =>
      sectionValue (planeLevi (binaryUnipotent coordinate) 1 * groupElement))
      additiveDomain adeleMeasure ∧
    (∫ coordinate in additiveDomain,
      sectionValue (planeLevi (binaryUnipotent coordinate) 1 * groupElement)
        ∂adeleMeasure) = 0 := by
  obtain ⟨vector, realized⟩ := induced.2.2.2.2.2 groupElement
  have orbit_value : (fun coordinate =>
      sectionValue (planeLevi (binaryUnipotent coordinate) 1 * groupElement)) =
      (fun coordinate => inducingData.cusp.realize vector (binaryUnipotent coordinate * 1)) := by
    funext coordinate
    have value := congrFun realized (binaryUnipotent coordinate)
    simpa only [det_binaryUnipotent, normPower_one, one_mul, mul_one] using value.symm
  rw [orbit_value]
  exact inducingData.cusp.cuspidal vector 1

theorem unitaryNormalize_binary_unipotent_cuspidal
    {degree : ℕ} {inducingData : InducingData degree}
    {family : ℂ → AdelicGL → ℂ}
    (induced : ∀ parameter, IsInduced inducingData .plane parameter (family parameter))
    (parameter : ℂ) (groupElement : AdelicGL) :
    IntegrableOn (fun coordinate =>
      unitaryNormalize degree family parameter (planeLevi (binaryUnipotent coordinate) 1 * groupElement))
      additiveDomain adeleMeasure ∧
    (∫ coordinate in additiveDomain,
      unitaryNormalize degree family parameter (planeLevi (binaryUnipotent coordinate) 1 * groupElement)
        ∂adeleMeasure) = 0 := by
  have original := induced_binary_unipotent_cuspidal
    (induced (parameter - ((degree : ℂ) + 3) / 2)) groupElement
  simp only [unitaryNormalize, map_mul, det_planeLevi, det_binaryUnipotent,
    one_mul, mul_one]
  exact ⟨original.1.const_mul _, by rw [integral_const_mul, original.2, mul_zero]⟩

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
