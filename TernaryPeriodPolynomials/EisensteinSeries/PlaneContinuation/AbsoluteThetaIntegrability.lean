module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.WeightedAbsoluteTheta

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularTransport
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.UpperTriangularChart TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspThetaDecay
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.WeightedAbsoluteTheta

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.AbsoluteThetaIntegrability

theorem large_log {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (fixed : vector.val ∈ fixedSubspace data.cusp finiteCongruence)
    (realTest : SchwartzMap RealSpace ℂ) (finiteTest : Rectangular FiniteAdeles → ℂ)
    (finiteContinuous : Continuous finiteTest) (finiteSupport : HasCompactSupport finiteTest)
    (point : AdelicGL) (power cuspPower : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ (integral : IntegralBinaryGL) (rotation : Circle)
      (scalarLog heightLog horizontal : ℝ), 0 ≤ scalarLog → 0 ≤ heightLog → |horizontal| ≤ 1 →
        Real.exp ((power : ℝ) * scalarLog + (cuspPower : ℝ) * heightLog) *
          base data vector (AdelicSchwartzTheta.tensorTest realTest finiteTest) point
            (AdelicSiegelCover.chart integral (SiegelMeasurability.scale scalarLog)
              (SiegelShells.argument horizontal heightLog) (RealSiegelSet.rightFactor rotation)) ≤ constant := by
  obtain ⟨constant, nonnegative, bounded⟩ := ChartAbsoluteDecay.large data vector fixed realTest finiteTest finiteContinuous finiteSupport
    (finiteParameters point) (finiteParameters_compact point) (realGroup point) RealSiegelSet.rightSet RealSiegelSet.rightSet_compact power cuspPower
  refine ⟨constant, nonnegative, fun integral rotation scalarLog heightLog horizontal scalarNonnegative heightNonnegative horizontalBound => ?_⟩
  rw [base_chart, Real.exp_add, Real.exp_nat_mul, Real.exp_nat_mul]
  exact bounded (finiteGroup point, GeneralLinearGroup.map integralEmbedding integral) ⟨integral, rfl⟩
    (RealSiegelSet.rightFactor rotation) ⟨rotation, rfl⟩ integral (SiegelShells.argument horizontal heightLog)
    (Real.exp_pos _) (Real.one_le_exp heightNonnegative) horizontalBound (Real.exp scalarLog) (Real.one_le_exp scalarNonnegative)

theorem small_log {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (fixed : vector.val ∈ fixedSubspace data.cusp finiteCongruence)
    (realTest : SchwartzMap RealSpace ℂ) (finiteTest : Rectangular FiniteAdeles → ℂ)
    (finiteContinuous : Continuous finiteTest) (finiteSupport : HasCompactSupport finiteTest)
    (point : AdelicGL) (cuspPower : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ (integral : IntegralBinaryGL) (rotation : Circle)
      (scalarLog heightLog horizontal : ℝ), 0 ≤ heightLog → |horizontal| ≤ 1 →
        Real.exp (7 * scalarLog + (cuspPower : ℝ) * heightLog) *
          base data vector (AdelicSchwartzTheta.tensorTest realTest finiteTest) point
            (AdelicSiegelCover.chart integral (SiegelMeasurability.scale scalarLog)
              (SiegelShells.argument horizontal heightLog) (RealSiegelSet.rightFactor rotation)) ≤ constant := by
  obtain ⟨constant, nonnegative, bounded⟩ := ChartAbsoluteDecay.small data vector fixed realTest finiteTest finiteContinuous finiteSupport
    (finiteParameters point) (finiteParameters_compact point) (realGroup point) RealSiegelSet.rightSet RealSiegelSet.rightSet_compact cuspPower
  refine ⟨constant, nonnegative, fun integral rotation scalarLog heightLog horizontal heightNonnegative horizontalBound => ?_⟩
  rw [base_chart, Real.exp_add, Real.exp_nat_mul]
  have scalarPower : Real.exp (7 * scalarLog) = Real.exp scalarLog ^ 7 := Real.exp_nat_mul scalarLog 7
  rw [scalarPower]
  exact bounded (finiteGroup point, GeneralLinearGroup.map integralEmbedding integral) ⟨integral, rfl⟩
    (RealSiegelSet.rightFactor rotation) ⟨rotation, rfl⟩ integral (SiegelShells.argument horizontal heightLog)
    (Real.exp_pos _) (Real.one_le_exp heightNonnegative) horizontalBound (Real.exp scalarLog) (Real.exp_pos _)

theorem integrable_domain {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (fixed : vector.val ∈ fixedSubspace data.cusp finiteCongruence)
    (realTest : SchwartzMap RealSpace ℂ) (finiteTest : Rectangular FiniteAdeles → ℂ)
    (finiteContinuous : Continuous finiteTest) (finiteSupport : HasCompactSupport finiteTest)
    (parameter : ℂ) (point : AdelicGL) (halfPlane : 7 < 2 * exponent degree parameter) :
    IntegrableOn (function data vector (AdelicSchwartzTheta.tensorTest realTest finiteTest) parameter point)
      BinaryFundamentalDomain.domain BinaryHaar.measure := by
  obtain ⟨power, powerBound⟩ := exists_nat_gt (2 * exponent degree parameter)
  obtain ⟨cuspPower, cuspBound⟩ := exists_nat_gt (exponent degree parameter)
  obtain ⟨largeConstant, largeNonnegative, largeBound⟩ := large_log data vector fixed realTest finiteTest finiteContinuous finiteSupport point power cuspPower
  obtain ⟨smallConstant, smallNonnegative, smallBound⟩ := small_log data vector fixed realTest finiteTest finiteContinuous finiteSupport point cuspPower
  let rate := min ((power : ℝ) - 2 * exponent degree parameter) (2 * exponent degree parameter - 7)
  have ratePositive : 0 < rate := lt_min (sub_pos.mpr powerBound) (sub_pos.mpr halfPlane)
  apply ShellDecay.integrable_domain _ (WeightedAbsoluteTheta.measurable data vector _
    (AdelicSchwartzTheta.tensorTest_continuous realTest finiteTest finiteContinuous) parameter point)
    (WeightedAbsoluteTheta.rational_invariant data vector _ parameter point)
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

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.AbsoluteThetaIntegrability
