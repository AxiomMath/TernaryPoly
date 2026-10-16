module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.PrimitiveTupleIdentity

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory Filter
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteRecoverySupport TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteMatrixWeight TernaryPeriodPolynomials.PlaneEisensteinContinuation.RecoveryCoefficients
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RecoveryOperatorLimit TernaryPeriodPolynomials.PlaneEisensteinContinuation.FinitePrimitiveRecovery

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.RecoveryHalfPlaneBounds

theorem coefficient_norm_mono {degree : ℕ} (data : InducingData degree) (first second : ℂ)
    (point : AdelicGL) (key : UniversalFiniteProfiles.Key data) (binary : BinaryFiniteGL)
    (integral : IntegralMatrix binary) (ordered : first.re ≤ second.re) :
    ‖coefficient data second point key binary‖ ≤ ‖coefficient data first point key binary‖ := by
  simp only [coefficient, norm_mul, inner_norm]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact Real.rpow_le_rpow_of_exponent_ge (weight_pos binary) (norm_le_one binary integral) (by linarith)

theorem difference_le {degree : ℕ} (data : InducingData degree) (reference parameter : ℂ)
    (point : AdelicGL) (pointIntegral : finiteGroup point ∈ Set.range (GeneralLinearGroup.map integralEmbedding))
    (key : UniversalFiniteProfiles.Key data) (number : ℕ) (ordered : (reference + number).re ≤ parameter.re)
    (binary : BinaryFiniteGL) :
    ‖coefficient data parameter point key binary - primitiveCoefficient data reference point key binary‖ ≤
      ‖coefficient data (reference + number) point key binary - primitiveCoefficient data reference point key binary‖ := by
  by_cases primitive : binary ∈ integralGroup
  · rw [primitiveCoefficient, Set.indicator_of_mem primitive,
      PrimitiveTupleIdentity.coefficient_parameter data parameter reference point key binary primitive,
      PrimitiveTupleIdentity.coefficient_parameter data (reference + number) reference point key binary primitive]
  · rw [primitiveCoefficient, Set.indicator_of_notMem primitive, sub_zero, sub_zero]
    by_cases integral : IntegralMatrix binary
    · exact coefficient_norm_mono data (reference + number) parameter point key binary integral ordered
    · rw [coefficient_supported data parameter point pointIntegral key binary integral,
        coefficient_supported data (reference + number) point pointIntegral key binary integral]

def error {degree : ℕ} (data : InducingData degree) (reference : ℂ) (point : AdelicGL)
    (key : UniversalFiniteProfiles.Key data) (number : ℕ) : ℝ :=
  ∫ binary, ‖coefficient data (reference + number) point key binary - primitiveCoefficient data reference point key binary‖
    ∂BinaryProductHaar.finiteMeasure

theorem error_nonnegative {degree : ℕ} (data : InducingData degree) (reference : ℂ) (point : AdelicGL)
    (key : UniversalFiniteProfiles.Key data) (number : ℕ) : 0 ≤ error data reference point key number :=
  integral_nonneg (fun _ => norm_nonneg _)

theorem error_tendsto {degree : ℕ} (data : InducingData degree) (reference : ℂ)
    (halfPlane : -(degree : ℝ) / 2 ≤ reference.re) (point : AdelicGL)
    (pointIntegral : finiteGroup point ∈ Set.range (GeneralLinearGroup.map integralEmbedding))
    (key : UniversalFiniteProfiles.Key data) : Tendsto (error data reference point key) atTop (nhds 0) :=
  difference_integral_tendsto data reference halfPlane point pointIntegral key

theorem operator_error_le {degree : ℕ} (data : InducingData degree) (reference parameter : ℂ)
    (halfPlane : -(degree : ℝ) / 2 ≤ reference.re) (point : AdelicGL)
    (pointIntegral : finiteGroup point ∈ Set.range (GeneralLinearGroup.map integralEmbedding))
    (key : UniversalFiniteProfiles.Key data) (number : ℕ) (ordered : (reference + number).re ≤ parameter.re) :
    ‖RecoveryCoefficients.operator data parameter ((shifted_halfPlane reference halfPlane number).trans ordered) point pointIntegral key -
      primitiveOperator data reference halfPlane point pointIntegral key‖ ≤ error data reference point key number := by
  calc
    _ ≤ ∫ binary, ‖coefficient data parameter point key binary - primitiveCoefficient data reference point key binary‖
        ∂BinaryProductHaar.finiteMeasure :=
      FiniteHilbertConvolution.operator_difference_bound data.cusp _ _
        (coefficient_integrable data parameter ((shifted_halfPlane reference halfPlane number).trans ordered) point pointIntegral key)
        (primitive_integrable data reference halfPlane point pointIntegral key)
    _ ≤ _ := integral_mono_ae
      ((coefficient_integrable data parameter ((shifted_halfPlane reference halfPlane number).trans ordered)
        point pointIntegral key).sub (primitive_integrable data reference halfPlane point pointIntegral key)).norm
      ((coefficient_integrable data (reference + number) (shifted_halfPlane reference halfPlane number)
        point pointIntegral key).sub (primitive_integrable data reference halfPlane point pointIntegral key)).norm
      (Eventually.of_forall (difference_le data reference parameter point pointIntegral key number ordered))

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.RecoveryHalfPlaneBounds
