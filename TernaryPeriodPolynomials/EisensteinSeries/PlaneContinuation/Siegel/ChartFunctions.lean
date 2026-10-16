module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.ChartAbsoluteDecay
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.ShellDecay

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularTransport
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.UpperTriangularChart TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspThetaDecay

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.SiegelChartFunctions

theorem real_projection_finite (point : GeneralLinearGroup (Fin 2) FiniteAdeles) :
    GeneralLinearGroup.map (RingHom.fst ℝ FiniteAdeles) (atFinite point) = 1 := by
  apply Units.ext
  rfl

theorem real_projection_infinite (point : BinaryRealGL) :
    GeneralLinearGroup.map (RingHom.fst ℝ FiniteAdeles) (atInfinity point) = point := by
  apply Units.ext
  rfl

theorem finite_projection_finite (point : GeneralLinearGroup (Fin 2) FiniteAdeles) :
    GeneralLinearGroup.map (RingHom.snd ℝ FiniteAdeles) (atFinite point) = point := by
  apply Units.ext
  rfl

theorem finite_projection_infinite (point : BinaryRealGL) :
    GeneralLinearGroup.map (RingHom.snd ℝ FiniteAdeles) (atInfinity point) = 1 := by
  apply Units.ext
  rfl

theorem real_projection_chart (integral : IntegralBinaryGL) (scale : ℝˣ) (argument : UpperHalfPlane) (right : BinaryRealGL) :
    GeneralLinearGroup.map (RingHom.fst ℝ FiniteAdeles) (AdelicSiegelCover.chart integral scale argument right) =
      GeneralLinearGroup.scalar (Fin 2) scale * (unit argument argument.im_pos * right) := by
  rw [AdelicSiegelCover.chart, map_mul, real_projection_finite, real_projection_infinite, one_mul]

theorem finite_projection_chart (integral : IntegralBinaryGL) (scale : ℝˣ) (argument : UpperHalfPlane) (right : BinaryRealGL) :
    GeneralLinearGroup.map (RingHom.snd ℝ FiniteAdeles) (AdelicSiegelCover.chart integral scale argument right) =
      GeneralLinearGroup.map integralEmbedding integral := by
  rw [AdelicSiegelCover.chart, map_mul, finite_projection_finite, finite_projection_infinite, mul_one]

theorem realTransform_scalar (point : GeneralLinearGroup (Fin 3) ℝ) (binary : BinaryRealGL)
    (scale : ℝˣ) (value : RealSpace) :
    realTransform point (GeneralLinearGroup.scalar (Fin 2) scale * binary) value =
      scale.val • realTransform point binary value := by
  obtain ⟨matrix, rfl⟩ := coordinateEquiv.surjective value
  rw [GeneralLinearGroup.scalar_commute, realTransform_apply, realTransform_apply, ← coordinateEquiv.map_smul]
  congr 1
  change point⁻¹.val * matrix * (binary.val * Matrix.diagonal (fun _ => scale.val)) =
    scale.val • (point⁻¹.val * matrix * binary.val)
  rw [← Matrix.mul_assoc]
  ext row column
  simp only [Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul, mul_comm]

theorem matrixTerm_chart (realTest : SchwartzMap RealSpace ℂ) (finiteTest : Rectangular FiniteAdeles → ℂ)
    (point : AdelicGL) (integral : IntegralBinaryGL) (scale : ℝˣ) (argument : UpperHalfPlane)
    (right : BinaryRealGL) (matrix : Rectangular ℚ) :
    RectangularTheta.matrixTerm (AdelicSchwartzTheta.tensorTest realTest finiteTest) point
        (AdelicSiegelCover.chart integral scale argument right) matrix =
      realTest (scale.val • realTransform (realGroup point) (unit argument argument.im_pos * right) (realVector matrix)) *
        FiniteParameterThetaDecay.pullback finiteTest (finiteGroup point, GeneralLinearGroup.map integralEmbedding integral) (finiteMatrix matrix) := by
  rw [AdelicSchwartzTheta.matrixTerm_factorization]
  simp only [AdelicSchwartzTheta.realPullback, AdelicSchwartzTheta.finitePullback,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
    real_projection_chart, finite_projection_chart, realTransform_scalar]
  rfl

theorem cusp_norm_chart {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (integral : IntegralBinaryGL) (scale : ℝˣ) (argument : UpperHalfPlane) (right : BinaryRealGL) :
    ‖data.cusp.realize vector (AdelicSiegelCover.chart integral scale argument right)‖ =
      ‖cuspValue data vector integral right argument argument.im_pos‖ := by
  rw [AdelicSiegelCover.chart, Height.atInfinity_mul, ← mul_assoc,
    TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel.atFinite_atInfinity_commute, mul_assoc,
    CohomologicalCenter.atInfinity_scalar, data.cusp.central, norm_mul, data.cusp.centralUnitary, one_mul]
  rfl

theorem rotation_det (rotation : Circle) : (RotationCircle.circleRotation rotation).val.det = 1 := by
  have normSquare := Complex.sq_norm (rotation : ℂ)
  rw [Circle.norm_coe, one_pow, Complex.normSq_apply] at normSquare
  change (RotationCircle.complexMatrix (rotation : ℂ)).det = 1
  rw [Matrix.det_fin_two]
  change (rotation : ℂ).re * (rotation : ℂ).re - (-(rotation : ℂ).im) * (rotation : ℂ).im = 1
  nlinarith

theorem rightFactor_det (rotation : Circle) : (RealSiegelSet.rightFactor rotation).val.det = 1 / 2 := by
  rw [RealSiegelSet.rightFactor, Units.val_mul, Matrix.det_mul, rotation_det, mul_one]
  norm_num [RealSiegelSet.half, BinaryStrongApproximation.diagonal, Matrix.det_fin_two]

theorem determinant_norm_chart (integral : IntegralBinaryGL) (scale : ℝˣ) (argument : UpperHalfPlane) (rotation : Circle) :
    (adeleNorm (GeneralLinearGroup.det (AdelicSiegelCover.chart integral scale argument (RealSiegelSet.rightFactor rotation))) : ℝ) =
      scale.val ^ 2 * argument.im / 2 := by
  rw [AdelicSiegelCover.chart, map_mul, map_mul, NNReal.coe_mul, TernaryPeriodPolynomials.PlaneEisensteinContinuation.Norm.adeleNorm_det_integral,
    NNReal.coe_one, one_mul, TernaryPeriodPolynomials.PlaneEisensteinContinuation.Norm.adeleNorm_det_atInfinity, Units.val_mul, Matrix.det_mul,
    Units.val_mul, Matrix.det_mul, rightFactor_det]
  have scalarDet : (GeneralLinearGroup.scalar (Fin 2) scale).val.det = scale.val ^ 2 := by
    change (GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 2) scale)).val = _
    rw [GeneralLinearGroup.det_scalar]
    rfl
  rw [scalarDet]
  change |scale.val ^ 2 * ((UpperTriangularChart.matrix argument).det * (1 / 2))| = _
  rw [matrix_det]
  change |scale.val ^ 2 * (argument.im * (1 / 2))| = _
  rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) (mul_nonneg argument.im_pos.le (by norm_num)))]
  ring

theorem determinant_log_chart (integral : IntegralBinaryGL) (scalarLog heightLog horizontal : ℝ) (rotation : Circle) :
    Real.log (adeleNorm (GeneralLinearGroup.det (AdelicSiegelCover.chart integral (SiegelMeasurability.scale scalarLog)
      (SiegelShells.argument horizontal heightLog) (RealSiegelSet.rightFactor rotation))) : ℝ) =
        2 * scalarLog + heightLog - Real.log 2 := by
  rw [determinant_norm_chart]
  change Real.log (Real.exp scalarLog ^ 2 * Real.exp heightLog / 2) = _
  rw [Real.log_div (by positivity) (by norm_num), Real.log_mul (by positivity) (Real.exp_ne_zero _),
    Real.log_pow, Real.log_exp, Real.log_exp]
  norm_num

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.SiegelChartFunctions
