module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Compact.VectorTheta
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Uniform.VectorIntegral
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.SeparateSupremum

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.SobolevSeminorms TernaryPeriodPolynomials.PlaneEisensteinContinuation.LargeThetaIntegral
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.ZeroConstantThetaDecay

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.CompactThetaIntegral

instance groupSecondCountable : SecondCountableTopology AdelicGL := by
  let _ : SecondCountableTopology (Matrix (Fin 3) (Fin 3) Adeles) :=
    inferInstanceAs (SecondCountableTopology (Fin 3 → Fin 3 → Adeles))
  let _ : SecondCountableTopology (Matrix (Fin 3) (Fin 3) Adeles)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  exact (Units.isEmbedding_embedProduct (M := Matrix (Fin 3) (Fin 3) Adeles)).secondCountableTopology

variable {Source : Type} [NormedAddCommGroup Source] [NormedSpace ℂ Source] [CompleteSpace Source]

theorem theta_bound {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (continuous : Continuous (fun vector => (family vector).val.val))
    (tests : Set (SchwartzMap RealSpace Source)) (bounded : UniformSchwartzBounds.Bounded tests)
    (finiteTest : Rectangular FiniteAdeles → ℂ) (finiteContinuous : Continuous finiteTest)
    (finiteSupport : HasCompactSupport finiteTest) (points : Set AdelicGL) (compact : IsCompact points)
    (binary : BinaryAdelicGL) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ test ∈ tests, ∀ point ∈ points,
      ‖VectorTheta.fullTheta data family (BanachAdelicTheta.tensorTest test finiteTest) point binary‖ ≤ bound := by
  obtain ⟨majorant, summable, nonnegative, bounds⟩ := UniformThetaMajorants.adelic tests bounded
    finiteTest finiteContinuous finiteSupport (points ×ˢ {binary}) (compact.prod isCompact_singleton)
  refine ⟨‖BanachCuspDecay.evaluation data family continuous binary‖ * ∑' matrix, majorant matrix,
    mul_nonneg (norm_nonneg _) (tsum_nonneg nonnegative), ?_⟩
  intro test testMembership point pointMembership
  have normSummable := BanachAdelicTheta.summable_norm test finiteTest finiteContinuous finiteSupport point binary
  exact ((BanachCuspDecay.evaluation data family continuous binary).le_opNorm _).trans
    (mul_le_mul_of_nonneg_left ((norm_tsum_le_tsum_norm normSummable).trans
      (normSummable.tsum_le_tsum (bounds test testMembership (point, binary) ⟨pointMembership, Set.mem_singleton binary⟩) summable))
      (norm_nonneg _))

theorem integrand_bound {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (continuous : Continuous (fun vector => (family vector).val.val))
    (tests : ℂ → SchwartzMap RealSpace Source)
    (finiteTest : Rectangular FiniteAdeles → ℂ) (finiteContinuous : Continuous finiteTest)
    (finiteSupport : HasCompactSupport finiteTest) (points : Set AdelicGL) (pointsCompact : IsCompact points)
    (parameters : Set ℂ) (compact : IsCompact parameters) (bounded : UniformSchwartzBounds.Bounded (tests '' parameters))
    (binary : BinaryAdelicGL) :
    ∃ bound : ℝ, ∀ parameter ∈ parameters, ∀ point ∈ points,
      ‖VectorThetaIntegral.integrand data family (BanachAdelicTheta.tensorTest (tests parameter) finiteTest)
        point parameter binary‖ ≤ bound := by
  obtain ⟨thetaBound, thetaNonnegative, thetaBounded⟩ := theta_bound data family continuous (tests '' parameters) bounded
    finiteTest finiteContinuous finiteSupport points pointsCompact binary
  obtain ⟨weight, weightBounded⟩ := compact.exists_bound_of_continuousOn (UniformVectorIntegral.exponent_continuous degree).continuousOn
  refine ⟨Real.exp (weight * |height binary|) * thetaBound, ?_⟩
  intro parameter parameterMembership point pointMembership
  rw [VectorThetaIntegral.norm_integrand]
  apply mul_le_mul _ (thetaBounded (tests parameter) ⟨parameter, parameterMembership, rfl⟩ point pointMembership)
    (norm_nonneg _) (Real.exp_pos _).le
  apply Real.exp_le_exp.mpr
  exact (le_abs_self _).trans (by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (weightBounded parameter parameterMembership) (abs_nonneg _))

theorem exists_bound {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (continuous : Continuous (fun vector => (family vector).val.val))
    (tests : ℂ → SchwartzMap RealSpace Source)
    (holomorphic : ∀ vector, Differentiable ℂ (fun parameter => tests parameter vector))
    (bounded : ∀ compact : Set ℂ, IsCompact compact → UniformSchwartzBounds.Bounded (tests '' compact))
    (zeroValue : ∀ parameter, tests parameter 0 = 0)
    (zeroFourier : ∀ parameter, FourierTransform.fourier (tests parameter) 0 = 0)
    (finiteScale : FiniteAdelesˣ) (offset : FiniteRectangularFourier.Space) (points : Set AdelicGL) (pointsCompact : IsCompact points)
    (parameters : Set ℂ) (compact : IsCompact parameters) :
    ∃ bound : BinaryAdelicGL → ℝ, IntegrableOn bound BinaryFundamentalDomain.domain BinaryHaar.measure ∧
      ∀ parameter ∈ parameters, ∀ point ∈ points, ∀ binary,
        ‖VectorThetaIntegral.integrand data family
          (BanachAdelicTheta.tensorTest (tests parameter) (RectangularAdelicPoisson.finiteTest finiteScale offset))
          point parameter binary‖ ≤ bound binary := by
  let integrands := fun parameter point => VectorThetaIntegral.integrand data family
    (BanachAdelicTheta.tensorTest (tests parameter) (RectangularAdelicPoisson.finiteTest finiteScale offset)) point parameter
  have measurable : ∀ parameter point, Measurable (integrands parameter point) := fun parameter point =>
    VectorThetaIntegral.integrand_measurable data family continuous (tests parameter) _
      (finiteTest_continuous finiteScale offset) (finiteTest_compactSupport finiteScale offset) point parameter
  have parameterContinuous : ∀ point binary, ContinuousOn (fun parameter => integrands parameter point binary) parameters := fun point binary =>
    (VectorThetaFamilies.integrand_differentiable data family continuous tests holomorphic bounded _
      (finiteTest_continuous finiteScale offset) (finiteTest_compactSupport finiteScale offset) point binary).continuous.continuousOn
  have pointContinuous : ∀ parameter binary, ContinuousOn (fun point => integrands parameter point binary) points := by
    intro parameter binary
    exact ((VectorTheta.fullTheta_continuous data family continuous (tests parameter) _
      (finiteTest_continuous finiteScale offset) (finiteTest_compactSupport finiteScale offset)).comp
        (continuous_id.prodMk continuous_const) |>.const_mul _).continuousOn
  let bound := SeparateSupremum.bound integrands parameters points
  have boundNonnegative : ∀ binary, 0 ≤ bound binary := SeparateSupremum.nonnegative integrands parameters points
  have boundMeasurable : Measurable bound := SeparateSupremum.measurable integrands parameters points
    (fun parameter _ point _ => measurable parameter point)
    (fun point _ binary => parameterContinuous point binary)
    (fun parameter _ binary => pointContinuous parameter binary)
  obtain ⟨weightBound, weightBounded⟩ := compact.exists_bound_of_continuousOn (UniformVectorIntegral.exponent_continuous degree).continuousOn
  let weight := max weightBound 0
  have weightNonnegative : 0 ≤ weight := le_max_right _ _
  have weightBounds : ∀ parameter ∈ parameters, |WeightedAbsoluteTheta.exponent degree parameter| ≤ weight := by
    intro parameter membership
    have result : |WeightedAbsoluteTheta.exponent degree parameter| ≤ weightBound := by
      simpa only [Real.norm_eq_abs] using weightBounded parameter membership
    exact result.trans (le_max_left _ _)
  obtain ⟨scalarPower, scalarPowerBound⟩ := exists_nat_gt (2 * weight)
  obtain ⟨cuspPower, cuspPowerBound⟩ := exists_nat_gt weight
  obtain ⟨largeConstant, largeNonnegative, largeBound⟩ := CompactVectorTheta.large_log data family continuous
    (tests '' parameters) (bounded parameters compact) finiteScale offset points pointsCompact scalarPower cuspPower
  obtain ⟨smallConstant, smallNonnegative, smallBound⟩ := CompactVectorTheta.small_log data family continuous
    (tests '' parameters) (bounded parameters compact) finiteScale offset points pointsCompact scalarPower cuspPower
  have integrable : IntegrableOn (fun binary => (bound binary : ℂ)) BinaryFundamentalDomain.domain BinaryHaar.measure := by
    refine ShellDecay.integrable_domain _ (Complex.measurable_ofReal.comp boundMeasurable) ?_
      ((largeConstant + smallConstant) * Real.exp (weight * |Real.log 2|))
      ((scalarPower : ℝ) - 2 * weight) ((cuspPower : ℝ) - weight)
      (by positivity) (sub_pos.mpr scalarPowerBound) (sub_pos.mpr cuspPowerBound) ?_
    · intro rational binary
      congr 1
      exact SeparateSupremum.congr integrands parameters points _ _ (fun parameter _ point _ =>
        VectorThetaIntegral.rational_invariant data family _ point parameter rational binary)
    · intro integer natural shellParameter
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (boundNonnegative _)]
      apply SeparateSupremum.bounded integrands parameters points _ _ (by positivity)
      intro parameter membership point pointMembership
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
        (fun nonnegative => largeBound (tests parameter) ⟨parameter, membership, rfl⟩ (zeroValue parameter) point pointMembership
          shellParameter.1 shellParameter.2.2.2.2 _ _ _ nonnegative heightNonnegative horizontal)
        (fun nonpositive => smallBound (tests parameter) ⟨parameter, membership, rfl⟩ (zeroFourier parameter) point pointMembership
          shellParameter.1 shellParameter.2.2.2.2 _ _ _ nonpositive heightNonnegative horizontal)
  refine ⟨bound, ?_, fun parameter membership point pointMembership binary =>
    SeparateSupremum.dominates integrands parameters points binary
      (integrand_bound data family continuous tests _ (finiteTest_continuous finiteScale offset)
        (finiteTest_compactSupport finiteScale offset) points pointsCompact parameters compact (bounded parameters compact) binary)
      parameter membership point pointMembership⟩
  change Integrable bound (BinaryHaar.measure.restrict BinaryFundamentalDomain.domain)
  apply integrable.norm.congr
  exact Filter.Eventually.of_forall (fun binary => by
    change ‖(bound binary : ℂ)‖ = bound binary
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (boundNonnegative binary)])

theorem total_measurable {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (continuous : Continuous (fun vector => (family vector).val.val))
    (test : SchwartzMap RealSpace Source) (finiteTest : Rectangular FiniteAdeles → ℂ)
    (finiteContinuous : Continuous finiteTest) (finiteSupport : HasCompactSupport finiteTest) (parameter : ℂ) :
    Measurable (fun point => VectorThetaIntegral.total data family (BanachAdelicTheta.tensorTest test finiteTest) point parameter) := by
  have joint : Measurable (fun pair : AdelicGL × BinaryAdelicGL =>
      VectorThetaIntegral.integrand data family (BanachAdelicTheta.tensorTest test finiteTest) pair.1 parameter pair.2) :=
    (((AdelicNormMeasurable.innerCharacter_measurable data parameter).comp
      WeightedAbsoluteTheta.determinant_continuous.measurable).comp measurable_snd).mul
        (VectorTheta.fullTheta_continuous data family continuous test finiteTest finiteContinuous finiteSupport).measurable
  exact (joint.stronglyMeasurable.integral_prod_right'
    (ν := BinaryHaar.measure.restrict BinaryFundamentalDomain.domain)).measurable

theorem total_bound {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (continuous : Continuous (fun vector => (family vector).val.val))
    (tests : ℂ → SchwartzMap RealSpace Source)
    (holomorphic : ∀ vector, Differentiable ℂ (fun parameter => tests parameter vector))
    (bounded : ∀ compact : Set ℂ, IsCompact compact → UniformSchwartzBounds.Bounded (tests '' compact))
    (zeroValue : ∀ parameter, tests parameter 0 = 0)
    (zeroFourier : ∀ parameter, FourierTransform.fourier (tests parameter) 0 = 0)
    (finiteScale : FiniteAdelesˣ) (offset : FiniteRectangularFourier.Space) (points : Set AdelicGL) (pointsCompact : IsCompact points)
    (parameters : Set ℂ) (compact : IsCompact parameters) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ parameter ∈ parameters, ∀ point ∈ points,
      ‖VectorThetaIntegral.total data family
        (BanachAdelicTheta.tensorTest (tests parameter) (RectangularAdelicPoisson.finiteTest finiteScale offset)) point parameter‖ ≤ bound := by
  obtain ⟨bound, integrable, bounds⟩ := exists_bound data family continuous tests holomorphic bounded zeroValue zeroFourier
    finiteScale offset points pointsCompact parameters compact
  refine ⟨∫ binary in BinaryFundamentalDomain.domain, ‖bound binary‖ ∂BinaryHaar.measure,
    integral_nonneg (fun binary => norm_nonneg _), ?_⟩
  intro parameter parameterMembership point pointMembership
  apply norm_integral_le_of_norm_le integrable.norm
  exact Filter.Eventually.of_forall (fun binary =>
    (bounds parameter parameterMembership point pointMembership binary).trans (le_abs_self _))

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.CompactThetaIntegral
