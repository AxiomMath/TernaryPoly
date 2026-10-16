module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Vector.AbsoluteTheta
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Compact.VectorTheta

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularTransport
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.SobolevSeminorms TernaryPeriodPolynomials.PlaneEisensteinContinuation.UpperTriangularChart
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.VectorAbsoluteTheta
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.CompactVectorTheta (finiteParameters finiteParameters_compact)

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.CompactAbsoluteThetaDecay

variable {Source : Type*} [NormedAddCommGroup Source] [NormedSpace ℂ Source] [CompleteSpace Source]

theorem large {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (continuous : Continuous (fun vector => (family vector).val.val))
    (realTest : SchwartzMap RealSpace Source) (finiteTest : Rectangular FiniteAdeles → ℂ)
    (finiteContinuous : Continuous finiteTest) (finiteSupport : HasCompactSupport finiteTest)
    (points : Set AdelicGL) (compact : IsCompact points) (rightSet : Set BinaryRealGL) (rightCompact : IsCompact rightSet)
    (power cuspPower : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ point ∈ points, ∀ right ∈ rightSet, ∀ (integral : IntegralBinaryGL) (argument : UpperHalfPlane),
      1 ≤ argument.im → |argument.re| ≤ 1 → ∀ scale : ℝˣ, 1 ≤ scale.val →
        scale.val ^ power * argument.im ^ cuspPower *
          base data family (BanachAdelicTheta.tensorTest realTest finiteTest) point
            (AdelicSiegelCover.chart integral scale argument right) ≤ constant := by
  obtain ⟨thetaConstant, thetaNonnegative, thetaBounded⟩ := BanachAbsoluteTheta.uniform_large realTest finiteTest
    finiteContinuous finiteSupport (finiteParameters points) (finiteParameters_compact points compact) power
  obtain ⟨distortion, distortionNonnegative, operatorBounded⟩ := CompactPointChartOperators.bounds (realGroup '' points) (compact.image InducedContinuity.realGroup_continuous) rightSet rightCompact
  obtain ⟨cuspConstant, cuspNonnegative, cuspBounded⟩ := VectorCuspThetaDecay.weighted_bound data family continuous rightSet rightCompact cuspPower
  let order := power + Module.finrank ℤ integerLattice + 1
  let thetaBound := thetaConstant * distortion ^ order
  refine ⟨cuspConstant * thetaBound, mul_nonneg cuspNonnegative (mul_nonneg thetaNonnegative (pow_nonneg distortionNonnegative _)), ?_⟩
  intro point pointMembership right rightMem integral argument height horizontal scale scaleLower
  let transform := realTransform (realGroup point) (unit argument argument.im_pos * right)
  obtain ⟨sourceSummable, sourceBound⟩ := thetaBounded
    (finiteGroup point, GeneralLinearGroup.map integralEmbedding integral) ⟨⟨point, pointMembership, rfl⟩, ⟨integral, rfl⟩⟩ transform.toContinuousLinearMap
    ‖transform.symm.toContinuousLinearMap‖ (norm_nonneg _) (AdelicThetaDistortion.inverse_norm_bound transform) scale.val scaleLower
  have thetaEstimate : scale.val ^ power * BanachAbsoluteTheta.absoluteTail realTest finiteTest
      (finiteGroup point, GeneralLinearGroup.map integralEmbedding integral) transform.toContinuousLinearMap scale.val ≤ thetaBound :=
    sourceBound.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _)
      (operatorBounded (realGroup point) ⟨point, pointMembership, rfl⟩ right rightMem argument argument.im_pos height horizontal).2.1 order) thetaNonnegative)
  calc
    _ = scale.val ^ power * (argument.im ^ cuspPower * base data family (BanachAdelicTheta.tensorTest realTest finiteTest) point
        (AdelicSiegelCover.chart integral scale argument right)) := by ring
    _ ≤ scale.val ^ power * (cuspConstant * BanachAbsoluteTheta.absoluteTail realTest finiteTest
        (finiteGroup point, GeneralLinearGroup.map integralEmbedding integral) transform.toContinuousLinearMap scale.val) :=
      mul_le_mul_of_nonneg_left (weighted_base_chart data family continuous realTest finiteTest finiteContinuous finiteSupport
        point integral scale argument right cuspPower cuspConstant (cuspBounded right rightMem integral argument) sourceSummable)
        (pow_nonneg (zero_le_one.trans scaleLower) _)
    _ = cuspConstant * (scale.val ^ power * BanachAbsoluteTheta.absoluteTail realTest finiteTest
        (finiteGroup point, GeneralLinearGroup.map integralEmbedding integral) transform.toContinuousLinearMap scale.val) := by ring
    _ ≤ cuspConstant * thetaBound := mul_le_mul_of_nonneg_left thetaEstimate cuspNonnegative

theorem small {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (continuous : Continuous (fun vector => (family vector).val.val))
    (realTest : SchwartzMap RealSpace Source) (finiteTest : Rectangular FiniteAdeles → ℂ)
    (finiteContinuous : Continuous finiteTest) (finiteSupport : HasCompactSupport finiteTest)
    (points : Set AdelicGL) (compact : IsCompact points) (rightSet : Set BinaryRealGL) (rightCompact : IsCompact rightSet) (cuspPower : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ point ∈ points, ∀ right ∈ rightSet, ∀ (integral : IntegralBinaryGL) (argument : UpperHalfPlane),
      1 ≤ argument.im → |argument.re| ≤ 1 → ∀ scale : ℝˣ, 0 < scale.val →
        scale.val ^ 7 * argument.im ^ cuspPower *
          base data family (BanachAdelicTheta.tensorTest realTest finiteTest) point
            (AdelicSiegelCover.chart integral scale argument right) ≤ constant := by
  obtain ⟨thetaConstant, thetaNonnegative, thetaBounded⟩ := BanachAbsoluteTheta.uniform_small realTest finiteTest
    finiteContinuous finiteSupport (finiteParameters points) (finiteParameters_compact points compact)
  obtain ⟨distortion, distortionNonnegative, operatorBounded⟩ := CompactPointChartOperators.bounds (realGroup '' points) (compact.image InducedContinuity.realGroup_continuous) rightSet rightCompact
  obtain ⟨cuspConstant, cuspNonnegative, cuspBounded⟩ := VectorCuspThetaDecay.weighted_bound data family continuous rightSet rightCompact cuspPower
  let thetaBound := thetaConstant * distortion ^ 7
  refine ⟨cuspConstant * thetaBound, mul_nonneg cuspNonnegative (mul_nonneg thetaNonnegative (pow_nonneg distortionNonnegative _)), ?_⟩
  intro point pointMembership right rightMem integral argument height horizontal scale scalePositive
  let transform := realTransform (realGroup point) (unit argument argument.im_pos * right)
  obtain ⟨sourceSummable, sourceBound⟩ := thetaBounded
    (finiteGroup point, GeneralLinearGroup.map integralEmbedding integral) ⟨⟨point, pointMembership, rfl⟩, ⟨integral, rfl⟩⟩ transform scale.val scalePositive
  have thetaEstimate : scale.val ^ 7 * BanachAbsoluteTheta.absoluteTail realTest finiteTest
      (finiteGroup point, GeneralLinearGroup.map integralEmbedding integral) transform.toContinuousLinearMap scale.val ≤ thetaBound :=
    sourceBound.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _)
      (operatorBounded (realGroup point) ⟨point, pointMembership, rfl⟩ right rightMem argument argument.im_pos height horizontal).2.1 7) thetaNonnegative)
  calc
    _ = scale.val ^ 7 * (argument.im ^ cuspPower * base data family (BanachAdelicTheta.tensorTest realTest finiteTest) point
        (AdelicSiegelCover.chart integral scale argument right)) := by ring
    _ ≤ scale.val ^ 7 * (cuspConstant * BanachAbsoluteTheta.absoluteTail realTest finiteTest
        (finiteGroup point, GeneralLinearGroup.map integralEmbedding integral) transform.toContinuousLinearMap scale.val) :=
      mul_le_mul_of_nonneg_left (weighted_base_chart data family continuous realTest finiteTest finiteContinuous finiteSupport
        point integral scale argument right cuspPower cuspConstant (cuspBounded right rightMem integral argument) sourceSummable)
        (pow_nonneg scalePositive.le _)
    _ = cuspConstant * (scale.val ^ 7 * BanachAbsoluteTheta.absoluteTail realTest finiteTest
        (finiteGroup point, GeneralLinearGroup.map integralEmbedding integral) transform.toContinuousLinearMap scale.val) := by ring
    _ ≤ cuspConstant * thetaBound := mul_le_mul_of_nonneg_left thetaEstimate cuspNonnegative

theorem large_log {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (continuous : Continuous (fun vector => (family vector).val.val))
    (realTest : SchwartzMap RealSpace Source) (finiteTest : Rectangular FiniteAdeles → ℂ)
    (finiteContinuous : Continuous finiteTest) (finiteSupport : HasCompactSupport finiteTest)
    (points : Set AdelicGL) (compact : IsCompact points) (power cuspPower : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ point ∈ points, ∀ (integral : IntegralBinaryGL) (rotation : Circle)
      (scalarLog heightLog horizontal : ℝ), 0 ≤ scalarLog → 0 ≤ heightLog → |horizontal| ≤ 1 →
        Real.exp ((power : ℝ) * scalarLog + (cuspPower : ℝ) * heightLog) *
          base data family (BanachAdelicTheta.tensorTest realTest finiteTest) point
            (AdelicSiegelCover.chart integral (SiegelMeasurability.scale scalarLog)
              (SiegelShells.argument horizontal heightLog) (RealSiegelSet.rightFactor rotation)) ≤ constant := by
  obtain ⟨constant, nonnegative, bounded⟩ := large data family continuous realTest finiteTest finiteContinuous finiteSupport
    points compact RealSiegelSet.rightSet RealSiegelSet.rightSet_compact power cuspPower
  refine ⟨constant, nonnegative, fun point pointMembership integral rotation scalarLog heightLog horizontal scalarNonnegative heightNonnegative horizontalBound => ?_⟩
  rw [Real.exp_add, Real.exp_nat_mul, Real.exp_nat_mul]
  simpa only [SiegelMeasurability.scale, Units.val_mk0, SiegelShells.argument, UpperHalfPlane.im] using
    bounded point pointMembership (RealSiegelSet.rightFactor rotation) ⟨rotation, rfl⟩ integral (SiegelShells.argument horizontal heightLog)
      (Real.one_le_exp heightNonnegative) horizontalBound (SiegelMeasurability.scale scalarLog) (Real.one_le_exp scalarNonnegative)

theorem small_log {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (continuous : Continuous (fun vector => (family vector).val.val))
    (realTest : SchwartzMap RealSpace Source) (finiteTest : Rectangular FiniteAdeles → ℂ)
    (finiteContinuous : Continuous finiteTest) (finiteSupport : HasCompactSupport finiteTest)
    (points : Set AdelicGL) (compact : IsCompact points) (cuspPower : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ point ∈ points, ∀ (integral : IntegralBinaryGL) (rotation : Circle)
      (scalarLog heightLog horizontal : ℝ), 0 ≤ heightLog → |horizontal| ≤ 1 →
        Real.exp (7 * scalarLog + (cuspPower : ℝ) * heightLog) *
          base data family (BanachAdelicTheta.tensorTest realTest finiteTest) point
            (AdelicSiegelCover.chart integral (SiegelMeasurability.scale scalarLog)
              (SiegelShells.argument horizontal heightLog) (RealSiegelSet.rightFactor rotation)) ≤ constant := by
  obtain ⟨constant, nonnegative, bounded⟩ := small data family continuous realTest finiteTest finiteContinuous finiteSupport
    points compact RealSiegelSet.rightSet RealSiegelSet.rightSet_compact cuspPower
  refine ⟨constant, nonnegative, fun point pointMembership integral rotation scalarLog heightLog horizontal heightNonnegative horizontalBound => ?_⟩
  rw [Real.exp_add, Real.exp_nat_mul]
  have scalarPower : Real.exp (7 * scalarLog) = Real.exp scalarLog ^ 7 := Real.exp_nat_mul scalarLog 7
  rw [scalarPower]
  simpa only [SiegelMeasurability.scale, Units.val_mk0, SiegelShells.argument, UpperHalfPlane.im] using
    bounded point pointMembership (RealSiegelSet.rightFactor rotation) ⟨rotation, rfl⟩ integral (SiegelShells.argument horizontal heightLog)
      (Real.one_le_exp heightNonnegative) horizontalBound (SiegelMeasurability.scale scalarLog) (Real.exp_pos _)

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.CompactAbsoluteThetaDecay
