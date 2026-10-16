module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Cusp.FunctionContinuity
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.ExponentialWeights

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularTransport
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.UpperTriangularChart TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspThetaDecay

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.WeightedAbsoluteTheta

def base {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (test : Rectangular Adeles → ℂ) (point : AdelicGL) (binary : BinaryAdelicGL) : ℝ :=
  AbsoluteTheta.tail test point binary * ‖data.cusp.realize vector binary‖

theorem base_nonnegative {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (test : Rectangular Adeles → ℂ) (point : AdelicGL) (binary : BinaryAdelicGL) :
    0 ≤ base data vector test point binary := mul_nonneg (AbsoluteTheta.tail_nonnegative _ _ _) (norm_nonneg _)

def function {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (test : Rectangular Adeles → ℂ) (parameter : ℂ) (point : AdelicGL) (binary : BinaryAdelicGL) : ℂ :=
  (base data vector test point binary : ℂ) * GodementIntegral.innerCharacter data parameter (GeneralLinearGroup.det binary)

def exponent (degree : ℕ) (parameter : ℂ) : ℝ :=
  (binaryInductionExponent degree .plane parameter + 2 * inductionExponent .plane parameter).re

theorem determinant_continuous : Continuous (GeneralLinearGroup.det (n := Fin 2) (R := Adeles)) := by
  apply Units.continuous_iff.mpr
  constructor
  · exact (Units.continuous_val (M := Matrix (Fin 2) (Fin 2) Adeles)).matrix_det
  · simp only [← map_inv]
    exact ((Units.continuous_val (M := Matrix (Fin 2) (Fin 2) Adeles)).comp continuous_inv).matrix_det

theorem measurable {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (test : Rectangular Adeles → ℂ) (continuousTest : Continuous test) (parameter : ℂ) (point : AdelicGL) :
    Measurable (function data vector test parameter point) :=
  (Complex.continuous_ofReal.measurable.comp ((AbsoluteTheta.tail_measurable test continuousTest point).mul
    (CuspFunctionContinuity.continuous data.cusp vector).norm.measurable)).mul
      ((AdelicNormMeasurable.innerCharacter_measurable data parameter).comp determinant_continuous.measurable)

theorem rational_invariant {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (test : Rectangular Adeles → ℂ) (parameter : ℂ) (point : AdelicGL) (rational : BinaryRationalGL) (binary : BinaryAdelicGL) :
    function data vector test parameter point (GeneralLinearGroup.map rationalAdele rational * binary) =
      function data vector test parameter point binary := by
  have characterValue : GodementIntegral.innerCharacter data parameter
      (GeneralLinearGroup.det (GeneralLinearGroup.map rationalAdele rational)) = 1 := by
    rw [GeneralLinearGroup.map_det]
    exact ThetaInvariance.innerCharacter_rational data parameter (GeneralLinearGroup.det rational)
  simp only [function, base, AbsoluteTheta.tail_rational_binary, data.cusp.leftRational,
    map_mul, characterValue, one_mul]

theorem inner_norm {degree : ℕ} (data : InducingData degree) (parameter : ℂ) (scalar : Adelesˣ) :
    ‖GodementIntegral.innerCharacter data parameter scalar‖ =
      Real.exp (exponent degree parameter * Real.log (adeleNorm scalar : ℝ)) := by
  change ‖(data.chi.toMonoidHom scalar)⁻¹ * normPower scalar _‖ = _
  rw [norm_mul, norm_inv, data.chi.unitary, inv_one, one_mul, Helpers.norm_normPower]
  rfl

theorem norm_function {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (test : Rectangular Adeles → ℂ) (parameter : ℂ) (point : AdelicGL) (binary : BinaryAdelicGL) :
    ‖function data vector test parameter point binary‖ =
      Real.exp (exponent degree parameter * Real.log (adeleNorm (GeneralLinearGroup.det binary) : ℝ)) *
        base data vector test point binary := by
  rw [function, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (base_nonnegative _ _ _ _ _), inner_norm, mul_comm]

def finiteParameters (point : AdelicGL) : Set FiniteParameterThetaDecay.Parameter :=
  Set.range (fun integral : IntegralBinaryGL => (finiteGroup point, GeneralLinearGroup.map integralEmbedding integral))

theorem finiteParameters_compact (point : AdelicGL) : IsCompact (finiteParameters point) :=
  isCompact_range (continuous_const.prodMk BinaryLevel.integralMap_continuous)

theorem base_chart {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (realTest : SchwartzMap RealSpace ℂ) (finiteTest : Rectangular FiniteAdeles → ℂ)
    (point : AdelicGL) (integral : IntegralBinaryGL) (scale : ℝˣ) (argument : UpperHalfPlane) (right : BinaryRealGL) :
    base data vector (AdelicSchwartzTheta.tensorTest realTest finiteTest) point (AdelicSiegelCover.chart integral scale argument right) =
      UniformAbsoluteTheta.absoluteTail realTest finiteTest (finiteGroup point, GeneralLinearGroup.map integralEmbedding integral)
        (realTransform (realGroup point) (unit argument argument.im_pos * right)).toContinuousLinearMap scale.val *
          ‖cuspValue data vector integral right argument argument.im_pos‖ := by
  rw [base, AbsoluteTheta.tail_chart, SiegelChartFunctions.cusp_norm_chart]

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.WeightedAbsoluteTheta
