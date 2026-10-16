module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Vector.CuspThetaDecay
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Vector.Theta
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.ZeroConstantThetaDecay

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularTransport
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.SobolevSeminorms TernaryPeriodPolynomials.PlaneEisensteinContinuation.UpperTriangularChart

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.VectorThetaDecay

variable {Source : Type*} [NormedAddCommGroup Source] [NormedSpace ℂ Source] [CompleteSpace Source]

omit [CompleteSpace Source] in
theorem theta_chart (realTest : SchwartzMap RealSpace Source) (finiteScale : FiniteAdelesˣ)
    (offset : FiniteRectangularFourier.Space) (point : AdelicGL) (integral : IntegralBinaryGL)
    (scale : ℝˣ) (argument : UpperHalfPlane) (right : BinaryRealGL) :
    BanachAdelicTheta.fullTheta (BanachAdelicTheta.tensorTest realTest (RectangularAdelicPoisson.finiteTest finiteScale offset)) point
      (AdelicSiegelCover.chart integral scale argument right) =
      BanachThetaPoisson.theta (BanachThetaPoisson.pullback realTest (realTransform (realGroup point) (unit argument argument.im_pos * right)))
        (FiniteFourierUniform.test finiteScale offset (finiteGroup point, GeneralLinearGroup.map integralEmbedding integral)) scale.val := by
  unfold BanachAdelicTheta.fullTheta BanachThetaPoisson.theta
  apply tsum_congr
  intro matrix
  rw [BanachAdelicTheta.matrixTerm_factorization _ _ (point, AdelicSiegelCover.chart integral scale argument right)]
  simp only [ThetaParameterBounds.realAction, ThetaParameterBounds.finiteAction,
    SiegelChartFunctions.real_projection_chart, SiegelChartFunctions.finite_projection_chart,
    SiegelChartFunctions.realTransform_scalar, BanachThetaPoisson.pullback_apply, map_smul]
  rfl

omit [CompleteSpace Source] in
theorem norm_chart {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (realTest : SchwartzMap RealSpace Source) (finiteScale : FiniteAdelesˣ)
    (offset : FiniteRectangularFourier.Space) (point : AdelicGL) (integral : IntegralBinaryGL)
    (scale : ℝˣ) (argument : UpperHalfPlane) (right : BinaryRealGL) :
    ‖VectorTheta.fullTheta data family (BanachAdelicTheta.tensorTest realTest (RectangularAdelicPoisson.finiteTest finiteScale offset)) point
      (AdelicSiegelCover.chart integral scale argument right)‖ =
      ‖VectorCuspThetaDecay.value data family
        (BanachThetaPoisson.theta (BanachThetaPoisson.pullback realTest (realTransform (realGroup point) (unit argument argument.im_pos * right)))
          (FiniteFourierUniform.test finiteScale offset (finiteGroup point, GeneralLinearGroup.map integralEmbedding integral)) scale.val)
        integral right argument‖ := by
  rw [VectorTheta.fullTheta, theta_chart, SiegelChartFunctions.cusp_norm_chart]
  rfl

theorem large_log {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (continuous : Continuous (fun vector => (family vector).val.val))
    (realTest : SchwartzMap RealSpace Source) (zeroValue : realTest 0 = 0)
    (finiteScale : FiniteAdelesˣ) (offset : FiniteRectangularFourier.Space)
    (point : AdelicGL) (power cuspPower : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ (integral : IntegralBinaryGL) (rotation : Circle)
      (scalarLog heightLog horizontal : ℝ), 0 ≤ scalarLog → 0 ≤ heightLog → |horizontal| ≤ 1 →
        Real.exp ((power : ℝ) * scalarLog + (cuspPower : ℝ) * heightLog) *
          ‖VectorTheta.fullTheta data family (BanachAdelicTheta.tensorTest realTest (RectangularAdelicPoisson.finiteTest finiteScale offset)) point
            (AdelicSiegelCover.chart integral (SiegelMeasurability.scale scalarLog)
              (SiegelShells.argument horizontal heightLog) (RealSiegelSet.rightFactor rotation))‖ ≤ constant := by
  obtain ⟨constant, nonnegative, bounded⟩ := VectorCuspThetaDecay.large data family continuous realTest zeroValue finiteScale offset
    (WeightedAbsoluteTheta.finiteParameters point) (WeightedAbsoluteTheta.finiteParameters_compact point)
    (realGroup point) RealSiegelSet.rightSet RealSiegelSet.rightSet_compact power cuspPower
  refine ⟨constant, nonnegative, fun integral rotation scalarLog heightLog horizontal scalarNonnegative heightNonnegative horizontalBound => ?_⟩
  rw [norm_chart, Real.exp_add, Real.exp_nat_mul, Real.exp_nat_mul]
  simpa only [SiegelMeasurability.scale, Units.val_mk0, SiegelShells.argument, UpperHalfPlane.im] using
    bounded (finiteGroup point, GeneralLinearGroup.map integralEmbedding integral) ⟨integral, rfl⟩
      (RealSiegelSet.rightFactor rotation) ⟨rotation, rfl⟩ integral (SiegelShells.argument horizontal heightLog)
      (Real.one_le_exp heightNonnegative) horizontalBound (Real.exp scalarLog) (Real.one_le_exp scalarNonnegative)

theorem small_log {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (continuous : Continuous (fun vector => (family vector).val.val))
    (realTest : SchwartzMap RealSpace Source) (zeroFourier : FourierTransform.fourier realTest 0 = 0)
    (finiteScale : FiniteAdelesˣ) (offset : FiniteRectangularFourier.Space)
    (point : AdelicGL) (power cuspPower : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ (integral : IntegralBinaryGL) (rotation : Circle)
      (scalarLog heightLog horizontal : ℝ), scalarLog ≤ 0 → 0 ≤ heightLog → |horizontal| ≤ 1 →
        Real.exp (-(power : ℝ) * scalarLog + (cuspPower : ℝ) * heightLog) *
          ‖VectorTheta.fullTheta data family (BanachAdelicTheta.tensorTest realTest (RectangularAdelicPoisson.finiteTest finiteScale offset)) point
            (AdelicSiegelCover.chart integral (SiegelMeasurability.scale scalarLog)
              (SiegelShells.argument horizontal heightLog) (RealSiegelSet.rightFactor rotation))‖ ≤ constant := by
  obtain ⟨constant, nonnegative, bounded⟩ := VectorCuspThetaDecay.small data family continuous realTest zeroFourier finiteScale offset
    (WeightedAbsoluteTheta.finiteParameters point) (WeightedAbsoluteTheta.finiteParameters_compact point)
    (realGroup point) RealSiegelSet.rightSet RealSiegelSet.rightSet_compact power cuspPower
  refine ⟨constant, nonnegative, fun integral rotation scalarLog heightLog horizontal scalarNonpositive heightNonnegative horizontalBound => ?_⟩
  rw [norm_chart, Real.exp_add, neg_mul, Real.exp_neg, Real.exp_nat_mul, ← inv_pow, Real.exp_nat_mul]
  simpa only [SiegelMeasurability.scale, Units.val_mk0, SiegelShells.argument, UpperHalfPlane.im] using
    bounded (finiteGroup point, GeneralLinearGroup.map integralEmbedding integral) ⟨integral, rfl⟩
      (RealSiegelSet.rightFactor rotation) ⟨rotation, rfl⟩ integral (SiegelShells.argument horizontal heightLog)
      (Real.one_le_exp heightNonnegative) horizontalBound (Real.exp scalarLog) (Real.exp_pos _)
      (Real.exp_le_one_iff.mpr scalarNonpositive)

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.VectorThetaDecay
