module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Binary.AdelicReduction

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteRotationTypes TernaryPeriodPolynomials.PlaneEisensteinContinuation.ClassicalCuspForms
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteClassicalComponents TernaryPeriodPolynomials.PlaneEisensteinContinuation.UpperTriangularChart

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.EndpointAdmissibility

theorem zero_on_positive_real {degree : ℕ} (data : InducingData degree)
    (vector : fixedMode data.cusp finiteCongruence (-(degree + 3 : ℤ)))
    (vanishing : finiteRealization data vector = 0) (integral : IntegralBinaryGL)
    (realMatrix : BinaryRealGL) (positive : 0 < (GeneralLinearGroup.det realMatrix).val) :
    data.cusp.realize vector.val
      (atFinite (GeneralLinearGroup.map integralEmbedding integral) * atInfinity realMatrix) = 0 := by
  let argument : UpperHalfPlane := ⟨Complex.I, by simp⟩
  have formZero := finiteRealization_determines_integral data vector vanishing integral
  have functionZero := congrArg (fun form : CuspForm ArithmeticModularity.arithmeticGroup (degree + 3) =>
    form (realMatrix • argument)) formZero
  have rawZero : raw data.cusp (atFinite (GeneralLinearGroup.map integralEmbedding integral)) vector.val
      (realMatrix • argument : UpperHalfPlane) = 0 :=
    (HolomorphicDecay.function_eq_zero_iff data.cusp _ vector.val (degree + 3) _).mp functionZero
  have transformed := MobiusChart.raw_transform data vector.val (-(degree + 3 : ℤ))
    (by simpa only [Int.cast_neg] using fixedMode_eigen data vector)
    (atFinite (GeneralLinearGroup.map integralEmbedding integral)) realMatrix positive argument
  rw [rawZero, mul_zero, raw_eq data.cusp _ vector.val argument argument.im_pos] at transformed
  simpa only [argument, HolomorphicRealization.unit_I, AveragingSmooth.atInfinity_one, mul_one] using transformed

theorem eq_zero_of_finiteRealization {degree : ℕ} (data : InducingData degree)
    (vector : fixedMode data.cusp finiteCongruence (-(degree + 3 : ℤ)))
    (vanishing : finiteRealization data vector = 0) : vector = 0 := by
  apply Subtype.ext
  apply data.cusp.injective
  funext point
  obtain ⟨rational, integral, realMatrix, positive, equality⟩ :=
    BinaryAdelicReduction.exists_rational_integral_positive point
  change data.cusp.realize vector.val point = data.cusp.realize (0 : data.cusp.smooth) point
  rw [map_zero, Pi.zero_apply, equality, data.cusp.leftRational]
  exact zero_on_positive_real data vector vanishing integral realMatrix positive

theorem finiteRealization_injective {degree : ℕ} (data : InducingData degree) :
    Function.Injective (finiteRealization data) :=
  LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr (eq_zero_of_finiteRealization data))

theorem negative_finiteDimensional {degree : ℕ} (data : InducingData degree) :
    FiniteDimensional ℂ (fixedMode data.cusp finiteCongruence (-(degree + 3 : ℤ))) :=
  finiteDimensional_of_injective data (finiteRealization_injective data)

theorem positive_finiteDimensional {degree : ℕ} (data : InducingData degree) :
    FiniteDimensional ℂ (fixedMode data.cusp finiteCongruence (degree + 3)) := by
  let _ := negative_finiteDimensional data
  exact ReflectionModes.finiteDimensional_of_neg data.cusp finiteCongruence (degree + 3)

theorem all_finiteDimensional {degree : ℕ} (data : InducingData degree) (index : ℤ) :
    FiniteDimensional ℂ (fixedMode data.cusp finiteCongruence index) := by
  let _ := positive_finiteDimensional data
  obtain ⟨vector, nonzero, eigen, lowest⟩ := CohomologicalCasimir.exists_lowest_weight data
  exact ReflectionModes.finite_types_of_lowest_weight data.cusp finiteCongruence (degree + 3)
    (by omega) vector nonzero eigen lowest index

theorem hasSum {degree : ℕ} {data : InducingData degree}
    {sectionFamily : ℂ → AdelicGL → ℂ} (flatSection : IsFlatSection data sectionFamily)
    (point : AdelicGL) (parameter : ℂ) (rightHalfPlane : -(degree : ℝ) / 2 < parameter.re) :
    HasSum (eisensteinSummand sectionFamily parameter point)
      (ScalarSeries.literalSum sectionFamily parameter point) := by
  let _ := positive_finiteDimensional data
  exact CohomologicalCasimir.hasSum_of_endpoint_finiteDimensional flatSection point parameter rightHalfPlane

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.EndpointAdmissibility
