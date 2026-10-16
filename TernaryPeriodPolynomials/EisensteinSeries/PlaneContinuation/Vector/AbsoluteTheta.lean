module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Banach.AbsoluteTheta
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Vector.ThetaIntegral

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularTransport
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.SobolevSeminorms TernaryPeriodPolynomials.PlaneEisensteinContinuation.UpperTriangularChart
open scoped Classical

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.VectorAbsoluteTheta

variable {Source : Type*} [NormedAddCommGroup Source] [NormedSpace ℂ Source] [CompleteSpace Source]

def tailTerm {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (test : Rectangular Adeles → Source) (point : AdelicGL) (binary : BinaryAdelicGL) (matrix : Rectangular ℚ) : ℂ :=
  if matrix = 0 then 0 else VectorTheta.term data family test point binary matrix

def base {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (test : Rectangular Adeles → Source) (point : AdelicGL) (binary : BinaryAdelicGL) : ℝ :=
  ∑' matrix, ‖tailTerm data family test point binary matrix‖

omit [CompleteSpace Source] in
theorem base_nonnegative {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (test : Rectangular Adeles → Source) (point : AdelicGL) (binary : BinaryAdelicGL) :
    0 ≤ base data family test point binary := tsum_nonneg (fun _ => norm_nonneg _)

theorem summable {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (continuous : Continuous (fun vector => (family vector).val.val))
    (realTest : SchwartzMap RealSpace Source) (finiteTest : Rectangular FiniteAdeles → ℂ)
    (finiteContinuous : Continuous finiteTest) (finiteSupport : HasCompactSupport finiteTest)
    (point : AdelicGL) (binary : BinaryAdelicGL) :
    Summable (fun matrix => ‖tailTerm data family (BanachAdelicTheta.tensorTest realTest finiteTest) point binary matrix‖) := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun matrix => ?_)
    (VectorTheta.summable_norm data family continuous realTest finiteTest finiteContinuous finiteSupport point binary)
  by_cases zero : matrix = 0
  · simp only [tailTerm, zero, ite_true, norm_zero]
    exact norm_nonneg _
  · simp only [tailTerm, ite_eq_right zero, le_refl]

omit [CompleteSpace Source] in
theorem term_rational_binary {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (test : Rectangular Adeles → Source) (point : AdelicGL) (binary : BinaryAdelicGL)
    (rational : BinaryRationalGL) (matrix : Rectangular ℚ) :
    VectorTheta.term data family test point (GeneralLinearGroup.map rationalAdele rational * binary) matrix =
      VectorTheta.term data family test point binary (RectangularTheta.rightEquiv rational matrix) := by
  rw [VectorTheta.term, VectorThetaIntegral.matrixTerm_rational_binary, data.cusp.leftRational]
  rfl

omit [CompleteSpace Source] in
theorem tailTerm_rational_binary {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (test : Rectangular Adeles → Source) (point : AdelicGL) (binary : BinaryAdelicGL)
    (rational : BinaryRationalGL) (matrix : Rectangular ℚ) :
    tailTerm data family test point (GeneralLinearGroup.map rationalAdele rational * binary) matrix =
      tailTerm data family test point binary (RectangularTheta.rightEquiv rational matrix) := by
  have nonzero : RectangularTheta.rightEquiv rational matrix = 0 ↔ matrix = 0 := by
    conv_lhs => rw [← AbsoluteTheta.rightEquiv_zero rational]
    exact (RectangularTheta.rightEquiv rational).injective.eq_iff
  simp only [tailTerm, nonzero, term_rational_binary]

omit [CompleteSpace Source] in
theorem base_rational_binary {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (test : Rectangular Adeles → Source) (point : AdelicGL) (binary : BinaryAdelicGL)
    (rational : BinaryRationalGL) :
    base data family test point (GeneralLinearGroup.map rationalAdele rational * binary) =
      base data family test point binary := by
  simp only [base, tailTerm_rational_binary]
  exact (RectangularTheta.rightEquiv rational).tsum_eq (fun matrix => ‖tailTerm data family test point binary matrix‖)

theorem term_continuous {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (continuous : Continuous (fun vector => (family vector).val.val))
    (test : Rectangular Adeles → Source) (testContinuous : Continuous test)
    (point : AdelicGL) (matrix : Rectangular ℚ) :
    Continuous (fun binary => tailTerm data family test point binary matrix) := by
  by_cases zero : matrix = 0
  · simp only [tailTerm, zero, ite_true]
    exact continuous_const
  · simp only [tailTerm, ite_eq_right zero]
    exact (VectorTheta.term_continuous data family continuous test testContinuous matrix).comp
      (f := fun binary : BinaryAdelicGL => (point, binary)) (continuous_const.prodMk continuous_id)

theorem base_measurable {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (continuous : Continuous (fun vector => (family vector).val.val))
    (test : Rectangular Adeles → Source) (testContinuous : Continuous test) (point : AdelicGL) :
    Measurable (base data family test point) := by
  let _ : Countable (Rectangular ℚ) := inferInstanceAs (Countable (Fin 3 → Fin 2 → ℚ))
  exact Measurable.tsum (fun matrix => (term_continuous data family continuous test testContinuous point matrix).norm.measurable)

def function {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (test : Rectangular Adeles → Source) (parameter : ℂ) (point : AdelicGL) (binary : BinaryAdelicGL) : ℂ :=
  (base data family test point binary : ℂ) * GodementIntegral.innerCharacter data parameter (GeneralLinearGroup.det binary)

theorem measurable {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (continuous : Continuous (fun vector => (family vector).val.val))
    (test : Rectangular Adeles → Source) (testContinuous : Continuous test) (parameter : ℂ) (point : AdelicGL) :
    Measurable (function data family test parameter point) :=
  (Complex.continuous_ofReal.measurable.comp (base_measurable data family continuous test testContinuous point)).mul
    ((AdelicNormMeasurable.innerCharacter_measurable data parameter).comp WeightedAbsoluteTheta.determinant_continuous.measurable)

omit [CompleteSpace Source] in
theorem rational_invariant {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (test : Rectangular Adeles → Source) (parameter : ℂ) (point : AdelicGL) (rational : BinaryRationalGL) (binary : BinaryAdelicGL) :
    function data family test parameter point (GeneralLinearGroup.map rationalAdele rational * binary) =
      function data family test parameter point binary := by
  have characterValue : GodementIntegral.innerCharacter data parameter
      (GeneralLinearGroup.det (GeneralLinearGroup.map rationalAdele rational)) = 1 := by
    rw [GeneralLinearGroup.map_det]
    exact ThetaInvariance.innerCharacter_rational data parameter (GeneralLinearGroup.det rational)
  simp only [function, base_rational_binary, map_mul, characterValue, one_mul]

omit [CompleteSpace Source] in
theorem norm_function {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (test : Rectangular Adeles → Source) (parameter : ℂ) (point : AdelicGL) (binary : BinaryAdelicGL) :
    ‖function data family test parameter point binary‖ =
      Real.exp (WeightedAbsoluteTheta.exponent degree parameter * Real.log (adeleNorm (GeneralLinearGroup.det binary) : ℝ)) *
        base data family test point binary := by
  rw [function, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (base_nonnegative _ _ _ _ _),
    WeightedAbsoluteTheta.inner_norm, mul_comm]

omit [CompleteSpace Source] in
theorem norm_tailTerm_chart {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (realTest : SchwartzMap RealSpace Source) (finiteTest : Rectangular FiniteAdeles → ℂ)
    (point : AdelicGL) (integral : IntegralBinaryGL) (scale : ℝˣ) (argument : UpperHalfPlane)
    (right : BinaryRealGL) (matrix : Rectangular ℚ) :
    ‖tailTerm data family (BanachAdelicTheta.tensorTest realTest finiteTest) point (AdelicSiegelCover.chart integral scale argument right) matrix‖ =
      ‖VectorCuspThetaDecay.value data family
        (BanachRationalUniformDecay.tailTerm realTest
          (FiniteParameterThetaDecay.pullback finiteTest (finiteGroup point, GeneralLinearGroup.map integralEmbedding integral))
          (realTransform (realGroup point) (unit argument argument.im_pos * right)).toContinuousLinearMap scale.val matrix)
        integral right argument‖ := by
  unfold tailTerm BanachRationalUniformDecay.tailTerm
  split_ifs
  · simp [VectorCuspThetaDecay.value, map_zero]
  · rw [VectorTheta.term, SiegelChartFunctions.cusp_norm_chart]
    congr 1
    change data.cusp.realize (family _).val _ = data.cusp.realize (family _).val _
    rw [BanachAdelicTheta.matrixTerm_factorization _ _ (point, AdelicSiegelCover.chart integral scale argument right)]
    simp only [ThetaParameterBounds.realAction, ThetaParameterBounds.finiteAction,
      SiegelChartFunctions.real_projection_chart, SiegelChartFunctions.finite_projection_chart,
      SiegelChartFunctions.realTransform_scalar]
    rfl

theorem weighted_base_chart {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (continuous : Continuous (fun vector => (family vector).val.val))
    (realTest : SchwartzMap RealSpace Source) (finiteTest : Rectangular FiniteAdeles → ℂ)
    (finiteContinuous : Continuous finiteTest) (finiteSupport : HasCompactSupport finiteTest)
    (point : AdelicGL) (integral : IntegralBinaryGL) (scale : ℝˣ) (argument : UpperHalfPlane)
    (right : BinaryRealGL) (power : ℕ) (bound : ℝ)
    (cuspBound : ∀ vector : Source, argument.im ^ power * ‖VectorCuspThetaDecay.value data family vector integral right argument‖ ≤ bound * ‖vector‖)
    (sourceSummable : Summable (fun matrix => ‖BanachRationalUniformDecay.tailTerm realTest
      (FiniteParameterThetaDecay.pullback finiteTest (finiteGroup point, GeneralLinearGroup.map integralEmbedding integral))
      (realTransform (realGroup point) (unit argument argument.im_pos * right)).toContinuousLinearMap scale.val matrix‖)) :
    argument.im ^ power * base data family (BanachAdelicTheta.tensorTest realTest finiteTest) point
        (AdelicSiegelCover.chart integral scale argument right) ≤
      bound * BanachAbsoluteTheta.absoluteTail realTest finiteTest (finiteGroup point, GeneralLinearGroup.map integralEmbedding integral)
        (realTransform (realGroup point) (unit argument argument.im_pos * right)).toContinuousLinearMap scale.val := by
  rw [base, BanachAbsoluteTheta.absoluteTail, ← tsum_mul_left, ← tsum_mul_left]
  apply (summable data family continuous realTest finiteTest finiteContinuous finiteSupport point
    (AdelicSiegelCover.chart integral scale argument right)).mul_left _ |>.tsum_le_tsum
    (fun matrix => ?_) (sourceSummable.mul_left bound)
  rw [norm_tailTerm_chart]
  exact cuspBound _

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.VectorAbsoluteTheta
