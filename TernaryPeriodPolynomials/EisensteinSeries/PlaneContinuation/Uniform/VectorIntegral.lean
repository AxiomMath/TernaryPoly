module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Vector.ThetaFamilies
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Uniform.VectorTheta
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Compact.FamilySupremum
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Uniform.ExponentialWeights
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.HolomorphicDominatedIntegral

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.SobolevSeminorms TernaryPeriodPolynomials.PlaneEisensteinContinuation.LargeThetaIntegral
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.ZeroConstantThetaDecay

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.UniformVectorIntegral

variable {Source : Type} [NormedAddCommGroup Source] [NormedSpace ℂ Source] [CompleteSpace Source]

omit [NormedAddCommGroup Source] [NormedSpace ℂ Source] [CompleteSpace Source] in
theorem exponent_continuous (degree : ℕ) : Continuous (WeightedAbsoluteTheta.exponent degree) := by
  unfold WeightedAbsoluteTheta.exponent binaryInductionExponent inductionExponent
  fun_prop

theorem exists_bound {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (continuous : Continuous (fun vector => (family vector).val.val))
    (tests : ℂ → SchwartzMap RealSpace Source)
    (holomorphic : ∀ vector, Differentiable ℂ (fun parameter => tests parameter vector))
    (bounded : ∀ compact : Set ℂ, IsCompact compact → UniformSchwartzBounds.Bounded (tests '' compact))
    (zeroValue : ∀ parameter, tests parameter 0 = 0)
    (zeroFourier : ∀ parameter, FourierTransform.fourier (tests parameter) 0 = 0)
    (finiteScale : FiniteAdelesˣ) (offset : FiniteRectangularFourier.Space) (point : AdelicGL)
    (parameters : Set ℂ) (compact : IsCompact parameters) :
    ∃ bound : BinaryAdelicGL → ℝ, IntegrableOn bound BinaryFundamentalDomain.domain BinaryHaar.measure ∧
      ∀ parameter ∈ parameters, ∀ binary,
        ‖VectorThetaIntegral.integrand data family
          (BanachAdelicTheta.tensorTest (tests parameter) (RectangularAdelicPoisson.finiteTest finiteScale offset))
          point parameter binary‖ ≤ bound binary := by
  let integrands := fun parameter => VectorThetaIntegral.integrand data family
    (BanachAdelicTheta.tensorTest (tests parameter) (RectangularAdelicPoisson.finiteTest finiteScale offset)) point parameter
  have measurable : ∀ parameter, Measurable (integrands parameter) := fun parameter =>
    VectorThetaIntegral.integrand_measurable data family continuous (tests parameter) _
      (finiteTest_continuous finiteScale offset) (finiteTest_compactSupport finiteScale offset) point parameter
  have parameterContinuous : ∀ binary, ContinuousOn (fun parameter => integrands parameter binary) parameters := fun binary =>
    (VectorThetaFamilies.integrand_differentiable data family continuous tests holomorphic bounded _
      (finiteTest_continuous finiteScale offset) (finiteTest_compactSupport finiteScale offset) point binary).continuous.continuousOn
  let bound := CompactFamilySupremum.bound integrands parameters
  have boundNonnegative : ∀ binary, 0 ≤ bound binary := CompactFamilySupremum.nonnegative integrands parameters
  have boundMeasurable : Measurable bound := CompactFamilySupremum.measurable integrands parameters
    (fun parameter _ => measurable parameter) parameterContinuous
  obtain ⟨weightBound, weightBounded⟩ := compact.exists_bound_of_continuousOn (exponent_continuous degree).continuousOn
  let weight := max weightBound 0
  have weightNonnegative : 0 ≤ weight := le_max_right _ _
  have weightBounds : ∀ parameter ∈ parameters, |WeightedAbsoluteTheta.exponent degree parameter| ≤ weight := by
    intro parameter membership
    have result : |WeightedAbsoluteTheta.exponent degree parameter| ≤ weightBound := by
      simpa only [Real.norm_eq_abs] using weightBounded parameter membership
    exact result.trans (le_max_left _ _)
  obtain ⟨scalarPower, scalarPowerBound⟩ := exists_nat_gt (2 * weight)
  obtain ⟨cuspPower, cuspPowerBound⟩ := exists_nat_gt weight
  obtain ⟨largeConstant, largeNonnegative, largeBound⟩ := UniformVectorTheta.large_log data family continuous
    (tests '' parameters) (bounded parameters compact) finiteScale offset point scalarPower cuspPower
  obtain ⟨smallConstant, smallNonnegative, smallBound⟩ := UniformVectorTheta.small_log data family continuous
    (tests '' parameters) (bounded parameters compact) finiteScale offset point scalarPower cuspPower
  have integrable : IntegrableOn (fun binary => (bound binary : ℂ)) BinaryFundamentalDomain.domain BinaryHaar.measure := by
    refine ShellDecay.integrable_domain _ (Complex.measurable_ofReal.comp boundMeasurable) ?_
      ((largeConstant + smallConstant) * Real.exp (weight * |Real.log 2|))
      ((scalarPower : ℝ) - 2 * weight) ((cuspPower : ℝ) - weight)
      (by positivity) (sub_pos.mpr scalarPowerBound) (sub_pos.mpr cuspPowerBound) ?_
    · intro rational binary
      congr 1
      exact CompactFamilySupremum.congr integrands parameters _ _ (fun parameter _ =>
        VectorThetaIntegral.rational_invariant data family _ point parameter rational binary)
    · intro integer natural shellParameter
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (boundNonnegative _)]
      apply CompactFamilySupremum.bounded integrands parameters _ _ (by positivity)
      intro parameter membership
      change ‖VectorThetaIntegral.integrand data family _ point parameter _‖ ≤ _
      rw [VectorThetaIntegral.norm_integrand]
      simp only [SiegelShells.parameterize, height, SiegelChartFunctions.determinant_log_chart]
      have heightNonnegative : 0 ≤ (natural : ℝ) + shellParameter.2.2.1.val :=
        add_nonneg (Nat.cast_nonneg _) shellParameter.2.2.1.property.1
      have horizontal : |shellParameter.2.2.2.1.val| ≤ 1 := abs_le.mpr shellParameter.2.2.2.1.property
      exact UniformExponentialWeights.two_rates _ largeConstant smallConstant scalarPower cuspPower
        (WeightedAbsoluteTheta.exponent degree parameter) weight
        ((integer : ℝ) + shellParameter.2.1.val) ((natural : ℝ) + shellParameter.2.2.1.val) (Real.log 2)
        largeNonnegative smallNonnegative (weightBounds parameter membership) heightNonnegative
        (fun nonnegative => largeBound (tests parameter) ⟨parameter, membership, rfl⟩ (zeroValue parameter)
          shellParameter.1 shellParameter.2.2.2.2 _ _ _ nonnegative heightNonnegative horizontal)
        (fun nonpositive => smallBound (tests parameter) ⟨parameter, membership, rfl⟩ (zeroFourier parameter)
          shellParameter.1 shellParameter.2.2.2.2 _ _ _ nonpositive heightNonnegative horizontal)
  refine ⟨bound, ?_, fun parameter membership binary =>
    CompactFamilySupremum.dominates integrands parameters compact parameterContinuous binary parameter membership⟩
  change Integrable bound (BinaryHaar.measure.restrict BinaryFundamentalDomain.domain)
  apply integrable.norm.congr
  exact Filter.Eventually.of_forall (fun binary => by
    change ‖(bound binary : ℂ)‖ = bound binary
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (boundNonnegative binary)])

theorem differentiable {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (continuous : Continuous (fun vector => (family vector).val.val))
    (tests : ℂ → SchwartzMap RealSpace Source)
    (holomorphic : ∀ vector, Differentiable ℂ (fun parameter => tests parameter vector))
    (bounded : ∀ compact : Set ℂ, IsCompact compact → UniformSchwartzBounds.Bounded (tests '' compact))
    (zeroValue : ∀ parameter, tests parameter 0 = 0)
    (zeroFourier : ∀ parameter, FourierTransform.fourier (tests parameter) 0 = 0)
    (finiteScale : FiniteAdelesˣ) (offset : FiniteRectangularFourier.Space) (point : AdelicGL) :
    Differentiable ℂ (fun parameter => VectorThetaIntegral.total data family
      (BanachAdelicTheta.tensorTest (tests parameter) (RectangularAdelicPoisson.finiteTest finiteScale offset)) point parameter) := by
  apply HolomorphicDominatedIntegral.differentiable
    (BinaryHaar.measure.restrict BinaryFundamentalDomain.domain)
    (fun parameter => VectorThetaIntegral.integrand data family
      (BanachAdelicTheta.tensorTest (tests parameter) (RectangularAdelicPoisson.finiteTest finiteScale offset)) point parameter)
    (fun parameter => VectorThetaIntegral.integrand_measurable data family continuous (tests parameter) _
      (finiteTest_continuous finiteScale offset) (finiteTest_compactSupport finiteScale offset) point parameter)
    (fun binary => VectorThetaFamilies.integrand_differentiable data family continuous tests holomorphic bounded _
      (finiteTest_continuous finiteScale offset) (finiteTest_compactSupport finiteScale offset) point binary)
  intro center
  obtain ⟨bound, integrable, bounds⟩ := exists_bound data family continuous tests holomorphic bounded zeroValue zeroFourier
    finiteScale offset point (Metric.closedBall center 2) (isCompact_closedBall center 2)
  exact ⟨bound, integrable, fun parameter membership => bounds parameter (Metric.ball_subset_closedBall membership)⟩

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.UniformVectorIntegral
