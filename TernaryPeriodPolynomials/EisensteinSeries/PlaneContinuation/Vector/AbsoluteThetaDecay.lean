module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Vector.AbsoluteTheta

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularTransport
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.SobolevSeminorms TernaryPeriodPolynomials.PlaneEisensteinContinuation.UpperTriangularChart
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.VectorAbsoluteTheta
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.WeightedAbsoluteTheta (finiteParameters finiteParameters_compact exponent)

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.VectorAbsoluteThetaDecay

variable {Source : Type*} [NormedAddCommGroup Source] [NormedSpace ℂ Source] [CompleteSpace Source]

theorem large {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (continuous : Continuous (fun vector => (family vector).val.val))
    (realTest : SchwartzMap RealSpace Source) (finiteTest : Rectangular FiniteAdeles → ℂ)
    (finiteContinuous : Continuous finiteTest) (finiteSupport : HasCompactSupport finiteTest)
    (point : AdelicGL) (rightSet : Set BinaryRealGL) (rightCompact : IsCompact rightSet)
    (power cuspPower : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ right ∈ rightSet, ∀ (integral : IntegralBinaryGL) (argument : UpperHalfPlane),
      1 ≤ argument.im → |argument.re| ≤ 1 → ∀ scale : ℝˣ, 1 ≤ scale.val →
        scale.val ^ power * argument.im ^ cuspPower *
          base data family (BanachAdelicTheta.tensorTest realTest finiteTest) point
            (AdelicSiegelCover.chart integral scale argument right) ≤ constant := by
  obtain ⟨thetaConstant, thetaNonnegative, thetaBounded⟩ := BanachAbsoluteTheta.uniform_large realTest finiteTest
    finiteContinuous finiteSupport (finiteParameters point) (finiteParameters_compact point) power
  obtain ⟨distortion, distortionNonnegative, operatorBounded⟩ := CompactChartOperators.bounds (realGroup point) rightSet rightCompact
  obtain ⟨cuspConstant, cuspNonnegative, cuspBounded⟩ := VectorCuspThetaDecay.weighted_bound data family continuous rightSet rightCompact cuspPower
  let order := power + Module.finrank ℤ integerLattice + 1
  let thetaBound := thetaConstant * distortion ^ order
  refine ⟨cuspConstant * thetaBound, mul_nonneg cuspNonnegative (mul_nonneg thetaNonnegative (pow_nonneg distortionNonnegative _)), ?_⟩
  intro right rightMem integral argument height horizontal scale scaleLower
  let transform := realTransform (realGroup point) (unit argument argument.im_pos * right)
  obtain ⟨sourceSummable, sourceBound⟩ := thetaBounded
    (finiteGroup point, GeneralLinearGroup.map integralEmbedding integral) ⟨integral, rfl⟩ transform.toContinuousLinearMap
    ‖transform.symm.toContinuousLinearMap‖ (norm_nonneg _) (AdelicThetaDistortion.inverse_norm_bound transform) scale.val scaleLower
  have thetaEstimate : scale.val ^ power * BanachAbsoluteTheta.absoluteTail realTest finiteTest
      (finiteGroup point, GeneralLinearGroup.map integralEmbedding integral) transform.toContinuousLinearMap scale.val ≤ thetaBound :=
    sourceBound.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _)
      (operatorBounded right rightMem argument argument.im_pos height horizontal).2.1 order) thetaNonnegative)
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
    (point : AdelicGL) (rightSet : Set BinaryRealGL) (rightCompact : IsCompact rightSet) (cuspPower : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ right ∈ rightSet, ∀ (integral : IntegralBinaryGL) (argument : UpperHalfPlane),
      1 ≤ argument.im → |argument.re| ≤ 1 → ∀ scale : ℝˣ, 0 < scale.val →
        scale.val ^ 7 * argument.im ^ cuspPower *
          base data family (BanachAdelicTheta.tensorTest realTest finiteTest) point
            (AdelicSiegelCover.chart integral scale argument right) ≤ constant := by
  obtain ⟨thetaConstant, thetaNonnegative, thetaBounded⟩ := BanachAbsoluteTheta.uniform_small realTest finiteTest
    finiteContinuous finiteSupport (finiteParameters point) (finiteParameters_compact point)
  obtain ⟨distortion, distortionNonnegative, operatorBounded⟩ := CompactChartOperators.bounds (realGroup point) rightSet rightCompact
  obtain ⟨cuspConstant, cuspNonnegative, cuspBounded⟩ := VectorCuspThetaDecay.weighted_bound data family continuous rightSet rightCompact cuspPower
  let thetaBound := thetaConstant * distortion ^ 7
  refine ⟨cuspConstant * thetaBound, mul_nonneg cuspNonnegative (mul_nonneg thetaNonnegative (pow_nonneg distortionNonnegative _)), ?_⟩
  intro right rightMem integral argument height horizontal scale scalePositive
  let transform := realTransform (realGroup point) (unit argument argument.im_pos * right)
  obtain ⟨sourceSummable, sourceBound⟩ := thetaBounded
    (finiteGroup point, GeneralLinearGroup.map integralEmbedding integral) ⟨integral, rfl⟩ transform scale.val scalePositive
  have thetaEstimate : scale.val ^ 7 * BanachAbsoluteTheta.absoluteTail realTest finiteTest
      (finiteGroup point, GeneralLinearGroup.map integralEmbedding integral) transform.toContinuousLinearMap scale.val ≤ thetaBound :=
    sourceBound.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _)
      (operatorBounded right rightMem argument argument.im_pos height horizontal).2.1 7) thetaNonnegative)
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
    (point : AdelicGL) (power cuspPower : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ (integral : IntegralBinaryGL) (rotation : Circle)
      (scalarLog heightLog horizontal : ℝ), 0 ≤ scalarLog → 0 ≤ heightLog → |horizontal| ≤ 1 →
        Real.exp ((power : ℝ) * scalarLog + (cuspPower : ℝ) * heightLog) *
          base data family (BanachAdelicTheta.tensorTest realTest finiteTest) point
            (AdelicSiegelCover.chart integral (SiegelMeasurability.scale scalarLog)
              (SiegelShells.argument horizontal heightLog) (RealSiegelSet.rightFactor rotation)) ≤ constant := by
  obtain ⟨constant, nonnegative, bounded⟩ := large data family continuous realTest finiteTest finiteContinuous finiteSupport
    point RealSiegelSet.rightSet RealSiegelSet.rightSet_compact power cuspPower
  refine ⟨constant, nonnegative, fun integral rotation scalarLog heightLog horizontal scalarNonnegative heightNonnegative horizontalBound => ?_⟩
  rw [Real.exp_add, Real.exp_nat_mul, Real.exp_nat_mul]
  simpa only [SiegelMeasurability.scale, Units.val_mk0, SiegelShells.argument, UpperHalfPlane.im] using
    bounded (RealSiegelSet.rightFactor rotation) ⟨rotation, rfl⟩ integral (SiegelShells.argument horizontal heightLog)
      (Real.one_le_exp heightNonnegative) horizontalBound (SiegelMeasurability.scale scalarLog) (Real.one_le_exp scalarNonnegative)

theorem small_log {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (continuous : Continuous (fun vector => (family vector).val.val))
    (realTest : SchwartzMap RealSpace Source) (finiteTest : Rectangular FiniteAdeles → ℂ)
    (finiteContinuous : Continuous finiteTest) (finiteSupport : HasCompactSupport finiteTest)
    (point : AdelicGL) (cuspPower : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ (integral : IntegralBinaryGL) (rotation : Circle)
      (scalarLog heightLog horizontal : ℝ), 0 ≤ heightLog → |horizontal| ≤ 1 →
        Real.exp (7 * scalarLog + (cuspPower : ℝ) * heightLog) *
          base data family (BanachAdelicTheta.tensorTest realTest finiteTest) point
            (AdelicSiegelCover.chart integral (SiegelMeasurability.scale scalarLog)
              (SiegelShells.argument horizontal heightLog) (RealSiegelSet.rightFactor rotation)) ≤ constant := by
  obtain ⟨constant, nonnegative, bounded⟩ := small data family continuous realTest finiteTest finiteContinuous finiteSupport
    point RealSiegelSet.rightSet RealSiegelSet.rightSet_compact cuspPower
  refine ⟨constant, nonnegative, fun integral rotation scalarLog heightLog horizontal heightNonnegative horizontalBound => ?_⟩
  rw [Real.exp_add, Real.exp_nat_mul]
  have scalarPower : Real.exp (7 * scalarLog) = Real.exp scalarLog ^ 7 := Real.exp_nat_mul scalarLog 7
  rw [scalarPower]
  simpa only [SiegelMeasurability.scale, Units.val_mk0, SiegelShells.argument, UpperHalfPlane.im] using
    bounded (RealSiegelSet.rightFactor rotation) ⟨rotation, rfl⟩ integral (SiegelShells.argument horizontal heightLog)
      (Real.one_le_exp heightNonnegative) horizontalBound (SiegelMeasurability.scale scalarLog) (Real.exp_pos _)

theorem integrable_domain {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (continuous : Continuous (fun vector => (family vector).val.val))
    (realTest : SchwartzMap RealSpace Source) (finiteTest : Rectangular FiniteAdeles → ℂ)
    (finiteContinuous : Continuous finiteTest) (finiteSupport : HasCompactSupport finiteTest)
    (parameter : ℂ) (point : AdelicGL) (halfPlane : 7 < 2 * exponent degree parameter) :
    IntegrableOn (function data family (BanachAdelicTheta.tensorTest realTest finiteTest) parameter point)
      BinaryFundamentalDomain.domain BinaryHaar.measure := by
  obtain ⟨power, powerBound⟩ := exists_nat_gt (2 * exponent degree parameter)
  obtain ⟨cuspPower, cuspBound⟩ := exists_nat_gt (exponent degree parameter)
  obtain ⟨largeConstant, largeNonnegative, largeBound⟩ := large_log data family continuous realTest finiteTest finiteContinuous finiteSupport point power cuspPower
  obtain ⟨smallConstant, smallNonnegative, smallBound⟩ := small_log data family continuous realTest finiteTest finiteContinuous finiteSupport point cuspPower
  let rate := min ((power : ℝ) - 2 * exponent degree parameter) (2 * exponent degree parameter - 7)
  have ratePositive : 0 < rate := lt_min (sub_pos.mpr powerBound) (sub_pos.mpr halfPlane)
  apply ShellDecay.integrable_domain _ (VectorAbsoluteTheta.measurable data family continuous _
    (BanachAdelicTheta.tensorTest_continuous realTest finiteTest finiteContinuous) parameter point)
    (VectorAbsoluteTheta.rational_invariant data family _ parameter point)
    ((largeConstant + smallConstant) * Real.exp (-exponent degree parameter * Real.log 2))
    rate ((cuspPower : ℝ) - exponent degree parameter) (by positivity) ratePositive (sub_pos.mpr cuspBound)
  intro integer natural shellParameter
  rw [norm_function]
  simp only [SiegelShells.parameterize, SiegelChartFunctions.determinant_log_chart]
  have height : 0 ≤ (natural : ℝ) + shellParameter.2.2.1.val := add_nonneg (Nat.cast_nonneg _) shellParameter.2.2.1.property.1
  have horizontal : |shellParameter.2.2.2.1.val| ≤ 1 := abs_le.mpr shellParameter.2.2.2.1.property
  exact ExponentialWeights.two_ends _ largeConstant smallConstant power cuspPower (exponent degree parameter)
    ((integer : ℝ) + shellParameter.2.1.val) ((natural : ℝ) + shellParameter.2.2.1.val) (Real.log 2)
    largeNonnegative smallNonnegative
    (fun nonnegative => largeBound shellParameter.1 shellParameter.2.2.2.2 _ _ _ nonnegative height horizontal)
    (fun _ => smallBound shellParameter.1 shellParameter.2.2.2.2 _ _ _ height horizontal)

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.VectorAbsoluteThetaDecay
