module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Compact.AbsoluteThetaDecay
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Compact.ThetaIntegral

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.SobolevSeminorms TernaryPeriodPolynomials.PlaneEisensteinContinuation.VectorAbsoluteTheta
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.WeightedAbsoluteTheta (exponent)

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.CompactAbsoluteThetaBound

variable {Source : Type} [NormedAddCommGroup Source] [NormedSpace ℂ Source] [CompleteSpace Source]

theorem term_continuous {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (continuous : Continuous (fun vector => (family vector).val.val))
    (test : Rectangular Adeles → Source) (testContinuous : Continuous test)
    (binary : BinaryAdelicGL) (matrix : Rectangular ℚ) :
    Continuous (fun point => tailTerm data family test point binary matrix) := by
  by_cases zero : matrix = 0
  · simp only [tailTerm, zero, ite_true]
    exact continuous_const
  · simp only [tailTerm, ite_eq_right zero]
    exact (VectorTheta.term_continuous data family continuous test testContinuous matrix).comp
      (f := fun point : AdelicGL => (point, binary)) (continuous_id.prodMk continuous_const)

theorem base_continuousOn {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (continuous : Continuous (fun vector => (family vector).val.val))
    (realTest : SchwartzMap RealSpace Source) (finiteTest : Rectangular FiniteAdeles → ℂ)
    (finiteContinuous : Continuous finiteTest) (finiteSupport : HasCompactSupport finiteTest)
    (points : Set AdelicGL) (compact : IsCompact points) (binary : BinaryAdelicGL) :
    ContinuousOn (fun point => base data family (BanachAdelicTheta.tensorTest realTest finiteTest) point binary) points := by
  have testsBounded : UniformSchwartzBounds.Bounded {realTest} := by
    intro weight order
    refine ⟨SchwartzMap.seminorm ℂ weight order realTest, apply_nonneg _ _, ?_⟩
    rintro test rfl
    exact le_rfl
  obtain ⟨majorant, summable, nonnegative, bounds⟩ := UniformThetaMajorants.adelic {realTest} testsBounded
    finiteTest finiteContinuous finiteSupport (points ×ˢ {binary}) (compact.prod isCompact_singleton)
  apply continuousOn_tsum (fun matrix =>
    (term_continuous data family continuous _ (BanachAdelicTheta.tensorTest_continuous realTest finiteTest finiteContinuous) binary matrix).norm.continuousOn)
    (summable.mul_left ‖BanachCuspDecay.evaluation data family continuous binary‖)
  intro matrix point membership
  rw [norm_norm]
  by_cases zero : matrix = 0
  · simp only [tailTerm, ite_eq_left zero, norm_zero]
    exact mul_nonneg (norm_nonneg _) (nonnegative matrix)
  · rw [tailTerm, ite_eq_right zero]
    exact ((BanachCuspDecay.evaluation data family continuous binary).le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (bounds realTest (Set.mem_singleton _) (point, binary)
        ⟨membership, Set.mem_singleton _⟩ matrix) (norm_nonneg _))

theorem function_continuousOn {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (continuous : Continuous (fun vector => (family vector).val.val))
    (realTest : SchwartzMap RealSpace Source) (finiteTest : Rectangular FiniteAdeles → ℂ)
    (finiteContinuous : Continuous finiteTest) (finiteSupport : HasCompactSupport finiteTest)
    (points : Set AdelicGL) (compact : IsCompact points) (parameter : ℂ) (binary : BinaryAdelicGL) :
    ContinuousOn (fun point => function data family (BanachAdelicTheta.tensorTest realTest finiteTest) parameter point binary) points :=
  (Complex.continuous_ofReal.comp_continuousOn
    (base_continuousOn data family continuous realTest finiteTest finiteContinuous finiteSupport points compact binary)).mul_const _

theorem exists_bound {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (continuous : Continuous (fun vector => (family vector).val.val))
    (realTest : SchwartzMap RealSpace Source) (finiteTest : Rectangular FiniteAdeles → ℂ)
    (finiteContinuous : Continuous finiteTest) (finiteSupport : HasCompactSupport finiteTest)
    (parameter : ℂ) (halfPlane : 7 < 2 * exponent degree parameter)
    (points : Set AdelicGL) (compact : IsCompact points) :
    ∃ bound : BinaryAdelicGL → ℝ, IntegrableOn bound BinaryFundamentalDomain.domain BinaryHaar.measure ∧
      ∀ point ∈ points, ∀ binary,
        ‖function data family (BanachAdelicTheta.tensorTest realTest finiteTest) parameter point binary‖ ≤ bound binary := by
  let functions : ℂ → AdelicGL → BinaryAdelicGL → ℂ := fun _ =>
    function data family (BanachAdelicTheta.tensorTest realTest finiteTest) parameter
  let bound := SeparateSupremum.bound functions {0} points
  have nonnegative : ∀ binary, 0 ≤ bound binary := SeparateSupremum.nonnegative functions {0} points
  have measurable : Measurable bound := SeparateSupremum.measurable functions {0} points
    (fun _ _ point _ => VectorAbsoluteTheta.measurable data family continuous _
      (BanachAdelicTheta.tensorTest_continuous realTest finiteTest finiteContinuous) parameter point)
    (fun _ _ _ => continuousOn_const)
    (fun _ _ binary => function_continuousOn data family continuous realTest finiteTest finiteContinuous finiteSupport points compact parameter binary)
  obtain ⟨power, powerBound⟩ := exists_nat_gt (2 * exponent degree parameter)
  obtain ⟨cuspPower, cuspBound⟩ := exists_nat_gt (exponent degree parameter)
  obtain ⟨largeConstant, largeNonnegative, largeBound⟩ := CompactAbsoluteThetaDecay.large_log data family continuous
    realTest finiteTest finiteContinuous finiteSupport points compact power cuspPower
  obtain ⟨smallConstant, smallNonnegative, smallBound⟩ := CompactAbsoluteThetaDecay.small_log data family continuous
    realTest finiteTest finiteContinuous finiteSupport points compact cuspPower
  let rate := min ((power : ℝ) - 2 * exponent degree parameter) (2 * exponent degree parameter - 7)
  have ratePositive : 0 < rate := lt_min (sub_pos.mpr powerBound) (sub_pos.mpr halfPlane)
  have integrable : IntegrableOn (fun binary => (bound binary : ℂ)) BinaryFundamentalDomain.domain BinaryHaar.measure := by
    refine ShellDecay.integrable_domain _ (Complex.measurable_ofReal.comp measurable) ?_
      ((largeConstant + smallConstant) * Real.exp (-exponent degree parameter * Real.log 2))
      rate ((cuspPower : ℝ) - exponent degree parameter) (by positivity) ratePositive (sub_pos.mpr cuspBound) ?_
    · intro rational binary
      congr 1
      exact SeparateSupremum.congr functions {0} points _ _ (fun _ _ point _ =>
        VectorAbsoluteTheta.rational_invariant data family _ parameter point rational binary)
    · intro integer natural shellParameter
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (nonnegative _)]
      apply SeparateSupremum.bounded functions {0} points _ _ (by positivity)
      intro _ _ point membership
      change ‖function data family (BanachAdelicTheta.tensorTest realTest finiteTest) parameter point _‖ ≤ _
      rw [norm_function]
      simp only [SiegelShells.parameterize, SiegelChartFunctions.determinant_log_chart]
      have height : 0 ≤ (natural : ℝ) + shellParameter.2.2.1.val :=
        add_nonneg (Nat.cast_nonneg _) shellParameter.2.2.1.property.1
      have horizontal : |shellParameter.2.2.2.1.val| ≤ 1 := abs_le.mpr shellParameter.2.2.2.1.property
      exact ExponentialWeights.two_ends _ largeConstant smallConstant power cuspPower (exponent degree parameter)
        ((integer : ℝ) + shellParameter.2.1.val) ((natural : ℝ) + shellParameter.2.2.1.val) (Real.log 2)
        largeNonnegative smallNonnegative
        (fun nonnegative => largeBound point membership shellParameter.1 shellParameter.2.2.2.2 _ _ _ nonnegative height horizontal)
        (fun _ => smallBound point membership shellParameter.1 shellParameter.2.2.2.2 _ _ _ height horizontal)
  refine ⟨bound, ?_, ?_⟩
  · apply integrable.norm.congr
    exact Filter.Eventually.of_forall (fun binary => by
      change ‖(bound binary : ℂ)‖ = bound binary
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (nonnegative binary)])
  · intro point membership binary
    obtain ⟨constant, bounded⟩ := compact.exists_bound_of_continuousOn
      (function_continuousOn data family continuous realTest finiteTest finiteContinuous finiteSupport points compact parameter binary)
    exact SeparateSupremum.dominates functions {0} points binary ⟨constant, fun _ _ => bounded⟩
      0 (Set.mem_singleton _) point membership

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.CompactAbsoluteThetaBound
