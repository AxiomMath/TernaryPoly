module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Helpers

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem normPower_mul (firstIdele secondIdele : Adelesˣ) (parameter : ℂ) :
    normPower (firstIdele * secondIdele) parameter =
      normPower firstIdele parameter * normPower secondIdele parameter := by
  have first_positive : 0 < (adeleNorm firstIdele : ℝ) := adeleNorm_pos firstIdele
  have second_positive : 0 < (adeleNorm secondIdele : ℝ) := adeleNorm_pos secondIdele
  simp only [normPower, map_mul, NNReal.coe_mul]
  rw [Real.log_mul first_positive.ne' second_positive.ne', Complex.ofReal_add,
    mul_add, Complex.exp_add]

theorem normPower_pow (idele : Adelesˣ) (power : ℕ) (parameter : ℂ) :
    normPower (idele ^ power) parameter = normPower idele ((power : ℂ) * parameter) := by
  simp only [normPower, map_pow, NNReal.coe_pow, Real.log_pow, Complex.ofReal_mul,
    Complex.ofReal_natCast]
  congr 1
  ring

theorem normPower_one (parameter : ℂ) : normPower 1 parameter = 1 := by
  simp [normPower]

theorem planeLevi_scalar (idele : Adelesˣ) :
    planeLevi (GeneralLinearGroup.scalar (Fin 2) idele) idele =
      GeneralLinearGroup.scalar (Fin 3) idele := by
  apply Units.ext
  apply Matrix.ext
  intro row column
  fin_cases row <;> fin_cases column <;>
    simp [planeLevi, planeBlock, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]

theorem induced_binary_scalar
    {degree : ℕ} {inducingData : InducingData degree}
    {parameter : ℂ} {sectionValue : AdelicGL → ℂ}
    (induced : IsInduced inducingData .plane parameter sectionValue)
    (idele : Adelesˣ) (groupElement : AdelicGL) :
    sectionValue (planeLevi (GeneralLinearGroup.scalar (Fin 2) idele) 1 * groupElement) =
      normPower idele (2 * binaryInductionExponent degree .plane parameter) *
        inducingData.cusp.centralCharacter idele * sectionValue groupElement := by
  obtain ⟨vector, realized⟩ := induced.2.2.2.2.2 groupElement
  have scalar_value := congrFun realized (GeneralLinearGroup.scalar (Fin 2) idele)
  have identity_value := congrFun realized (1 : BinaryAdelicGL)
  have central_value := inducingData.cusp.central idele vector (1 : BinaryAdelicGL)
  rw [mul_one] at central_value
  rw [central_value, GeneralLinearGroup.det_scalar, Fintype.card_fin,
    normPower_pow] at scalar_value
  rw [map_one, normPower_one, one_mul] at identity_value
  have levi_one : planeLevi (1 : BinaryAdelicGL) 1 = 1 :=
    (planeLeviHom Adeles).map_one
  rw [levi_one, one_mul] at identity_value
  rw [identity_value] at scalar_value
  change inducingData.cusp.centralCharacter idele * sectionValue groupElement =
    normPower idele (2 * -binaryInductionExponent degree .plane parameter) *
      sectionValue (planeLevi (GeneralLinearGroup.scalar (Fin 2) idele) 1 *
        groupElement) at scalar_value
  have inverse_product :
      normPower idele (2 * binaryInductionExponent degree .plane parameter) *
        normPower idele (2 * -binaryInductionExponent degree .plane parameter) = 1 := by
    rw [← normPower_add]
    have exponent_zero :
        2 * binaryInductionExponent degree .plane parameter +
          2 * -binaryInductionExponent degree .plane parameter = 0 := by ring
    rw [exponent_zero, normPower_zero]
  calc
    sectionValue (planeLevi (GeneralLinearGroup.scalar (Fin 2) idele) 1 * groupElement) =
        normPower idele (2 * binaryInductionExponent degree .plane parameter) *
          (normPower idele (2 * -binaryInductionExponent degree .plane parameter) *
            sectionValue (planeLevi (GeneralLinearGroup.scalar (Fin 2) idele) 1 *
              groupElement)) := by rw [← mul_assoc, inverse_product, one_mul]
    _ = _ := by rw [← scalar_value, mul_assoc]

theorem induced_central_character
    {degree : ℕ} {inducingData : InducingData degree}
    {parameter : ℂ} {sectionValue : AdelicGL → ℂ}
    (induced : IsInduced inducingData .plane parameter sectionValue)
    (idele : Adelesˣ) (groupElement : AdelicGL) :
    sectionValue (GeneralLinearGroup.scalar (Fin 3) idele * groupElement) =
      inducingData.chi.toMonoidHom idele * inducingData.cusp.centralCharacter idele *
        normPower idele ((degree : ℂ) + 3) * sectionValue groupElement := by
  have levi_product :
      planeLevi (1 : BinaryAdelicGL) idele *
        planeLevi (GeneralLinearGroup.scalar (Fin 2) idele) 1 =
      GeneralLinearGroup.scalar (Fin 3) idele := by
    change (planeLeviHom Adeles) (1, idele) *
      (planeLeviHom Adeles) (GeneralLinearGroup.scalar (Fin 2) idele, 1) = _
    rw [← map_mul]
    change planeLevi (1 * GeneralLinearGroup.scalar (Fin 2) idele) (idele * 1) = _
    rw [one_mul, mul_one, planeLevi_scalar]
  rw [← levi_product, mul_assoc, induced.2.2.2.2.1,
    induced_binary_scalar induced idele groupElement]
  have exponents :
      -2 * inductionExponent .plane parameter +
        2 * binaryInductionExponent degree .plane parameter = (degree : ℂ) + 3 := by
    simp only [binaryInductionExponent]
    ring
  calc
    _ = inducingData.chi.toMonoidHom idele * inducingData.cusp.centralCharacter idele *
        (normPower idele (-2 * inductionExponent .plane parameter) *
          normPower idele (2 * binaryInductionExponent degree .plane parameter)) *
        sectionValue groupElement := by ring
    _ = _ := by rw [← normPower_add, exponents]

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
