module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.LargeThetaIntegral

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularTransport
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.UpperTriangularChart TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspThetaDecay

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.ZeroConstantThetaDecay

theorem finiteTest_continuous (scale : FiniteAdelesˣ) (offset : FiniteRectangularFourier.Space) :
    Continuous (RectangularAdelicPoisson.finiteTest scale offset) :=
  (FiniteRectangularFourier.boxTest_continuous (fun _ => scale) offset).comp AdelicThetaDecay.coordinateHomeomorph.continuous

theorem finiteTest_compactSupport (scale : FiniteAdelesˣ) (offset : FiniteRectangularFourier.Space) :
    HasCompactSupport (RectangularAdelicPoisson.finiteTest scale offset) :=
  (FiniteRectangularFourier.boxTest_compactSupport (fun _ => scale) offset).comp_homeomorph AdelicThetaDecay.coordinateHomeomorph

def base {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (test : Rectangular Adeles → ℂ) (point : AdelicGL) (binary : BinaryAdelicGL) : ℝ :=
  ‖RectangularTheta.fullTheta test point binary‖ * ‖data.cusp.realize vector binary‖

theorem theta_chart (realTest : SchwartzMap RealSpace ℂ) (finiteScale : FiniteAdelesˣ)
    (offset : FiniteRectangularFourier.Space) (point : AdelicGL) (integral : IntegralBinaryGL)
    (scale : ℝˣ) (argument : UpperHalfPlane) (right : BinaryRealGL) :
    RectangularTheta.fullTheta (AdelicSchwartzTheta.tensorTest realTest (RectangularAdelicPoisson.finiteTest finiteScale offset)) point
      (AdelicSiegelCover.chart integral scale argument right) =
      AdelicThetaDecay.theta (AdelicThetaDistortion.pullback realTest (realTransform (realGroup point) (unit argument argument.im_pos * right)))
        (FiniteFourierUniform.test finiteScale offset (finiteGroup point, GeneralLinearGroup.map integralEmbedding integral)) scale.val := by
  rw [← AdelicThetaDistortion.matrix_sum]
  unfold RectangularTheta.fullTheta
  apply tsum_congr
  intro matrix
  rw [SiegelChartFunctions.matrixTerm_chart]
  rfl

theorem base_chart {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (realTest : SchwartzMap RealSpace ℂ) (finiteScale : FiniteAdelesˣ)
    (offset : FiniteRectangularFourier.Space) (point : AdelicGL) (integral : IntegralBinaryGL)
    (scale : ℝˣ) (argument : UpperHalfPlane) (right : BinaryRealGL) :
    base data vector (AdelicSchwartzTheta.tensorTest realTest (RectangularAdelicPoisson.finiteTest finiteScale offset)) point
      (AdelicSiegelCover.chart integral scale argument right) =
      ‖AdelicThetaDecay.theta (AdelicThetaDistortion.pullback realTest (realTransform (realGroup point) (unit argument argument.im_pos * right)))
        (FiniteFourierUniform.test finiteScale offset (finiteGroup point, GeneralLinearGroup.map integralEmbedding integral)) scale.val *
          cuspValue data vector integral right argument argument.im_pos‖ := by
  rw [base, theta_chart, SiegelChartFunctions.cusp_norm_chart, norm_mul]

theorem large_log {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (fixed : vector.val ∈ fixedSubspace data.cusp finiteCongruence)
    (realTest : SchwartzMap RealSpace ℂ) (zeroValue : realTest 0 = 0)
    (finiteScale : FiniteAdelesˣ) (offset : FiniteRectangularFourier.Space)
    (point : AdelicGL) (power cuspPower : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ (integral : IntegralBinaryGL) (rotation : Circle)
      (scalarLog heightLog horizontal : ℝ), 0 ≤ scalarLog → 0 ≤ heightLog → |horizontal| ≤ 1 →
        Real.exp ((power : ℝ) * scalarLog + (cuspPower : ℝ) * heightLog) *
          base data vector (AdelicSchwartzTheta.tensorTest realTest (RectangularAdelicPoisson.finiteTest finiteScale offset)) point
            (AdelicSiegelCover.chart integral (SiegelMeasurability.scale scalarLog)
              (SiegelShells.argument horizontal heightLog) (RealSiegelSet.rightFactor rotation)) ≤ constant := by
  obtain ⟨constant, nonnegative, bounded⟩ := UniformCuspThetaDecay.large data vector fixed realTest finiteScale offset
    (WeightedAbsoluteTheta.finiteParameters point) (WeightedAbsoluteTheta.finiteParameters_compact point)
    (realGroup point) RealSiegelSet.rightSet RealSiegelSet.rightSet_compact power cuspPower
  refine ⟨constant, nonnegative, fun integral rotation scalarLog heightLog horizontal scalarNonnegative heightNonnegative horizontalBound => ?_⟩
  rw [base_chart, Real.exp_add, Real.exp_nat_mul, Real.exp_nat_mul]
  simpa only [zeroValue, zero_mul, sub_zero, SiegelMeasurability.scale, Units.val_mk0, SiegelShells.argument] using
    bounded (finiteGroup point, GeneralLinearGroup.map integralEmbedding integral) ⟨integral, rfl⟩
      (RealSiegelSet.rightFactor rotation) ⟨rotation, rfl⟩ integral (SiegelShells.argument horizontal heightLog)
      (Real.exp_pos _) (Real.one_le_exp heightNonnegative) horizontalBound (Real.exp scalarLog) (Real.one_le_exp scalarNonnegative)

theorem small_log {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (fixed : vector.val ∈ fixedSubspace data.cusp finiteCongruence)
    (realTest : SchwartzMap RealSpace ℂ) (zeroFourier : FourierTransform.fourier realTest 0 = 0)
    (finiteScale : FiniteAdelesˣ) (offset : FiniteRectangularFourier.Space)
    (point : AdelicGL) (power cuspPower : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ (integral : IntegralBinaryGL) (rotation : Circle)
      (scalarLog heightLog horizontal : ℝ), scalarLog ≤ 0 → 0 ≤ heightLog → |horizontal| ≤ 1 →
        Real.exp (-(power : ℝ) * scalarLog + (cuspPower : ℝ) * heightLog) *
          base data vector (AdelicSchwartzTheta.tensorTest realTest (RectangularAdelicPoisson.finiteTest finiteScale offset)) point
            (AdelicSiegelCover.chart integral (SiegelMeasurability.scale scalarLog)
              (SiegelShells.argument horizontal heightLog) (RealSiegelSet.rightFactor rotation)) ≤ constant := by
  obtain ⟨constant, nonnegative, bounded⟩ := UniformCuspThetaDecay.small data vector fixed realTest finiteScale offset
    (WeightedAbsoluteTheta.finiteParameters point) (WeightedAbsoluteTheta.finiteParameters_compact point)
    (realGroup point) RealSiegelSet.rightSet RealSiegelSet.rightSet_compact power cuspPower
  refine ⟨constant, nonnegative, fun integral rotation scalarLog heightLog horizontal scalarNonpositive heightNonnegative horizontalBound => ?_⟩
  rw [base_chart, Real.exp_add, neg_mul, Real.exp_neg, Real.exp_nat_mul, ← inv_pow, Real.exp_nat_mul]
  simpa only [zeroFourier, zero_mul, mul_zero, sub_zero, SiegelMeasurability.scale, Units.val_mk0, SiegelShells.argument] using
    bounded (finiteGroup point, GeneralLinearGroup.map integralEmbedding integral) ⟨integral, rfl⟩
      (RealSiegelSet.rightFactor rotation) ⟨rotation, rfl⟩ integral (SiegelShells.argument horizontal heightLog)
      (Real.exp_pos _) (Real.one_le_exp heightNonnegative) horizontalBound (Real.exp scalarLog) (Real.exp_pos _)
      (Real.exp_le_one_iff.mpr scalarNonpositive)

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.ZeroConstantThetaDecay
