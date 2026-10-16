module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.ZeroConstantThetaDecay

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory Filter
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz TernaryPeriodPolynomials.PlaneEisensteinContinuation.ZeroConstantThetaDecay
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.LargeThetaIntegral

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.ZeroConstantThetaIntegral

theorem tensor_zero (realTest : SchwartzMap RealSpace ℂ) (zeroValue : realTest 0 = 0)
    (finiteTest : Rectangular FiniteAdeles → ℂ) : AdelicSchwartzTheta.tensorTest realTest finiteTest 0 = 0 := by
  change realTest 0 * finiteTest 0 = 0
  rw [zeroValue, zero_mul]

theorem norm_integrand {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (realTest : SchwartzMap RealSpace ℂ) (zeroValue : realTest 0 = 0) (finiteTest : Rectangular FiniteAdeles → ℂ)
    (point : AdelicGL) (parameter : ℂ) (binary : BinaryAdelicGL) :
    ‖integrand data (AdelicSchwartzTheta.tensorTest realTest finiteTest) vector point parameter binary‖ =
      Real.exp (WeightedAbsoluteTheta.exponent degree parameter * height binary) *
        base data vector (AdelicSchwartzTheta.tensorTest realTest finiteTest) point binary := by
  rw [integrand, tensor_zero realTest zeroValue, sub_zero, norm_mul, norm_mul, WeightedAbsoluteTheta.inner_norm]
  unfold base height
  ring

theorem rational_invariant {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (test : Rectangular Adeles → ℂ) (point : AdelicGL) (parameter : ℂ) (rational : BinaryRationalGL) (binary : BinaryAdelicGL) :
    integrand data test vector point parameter (GeneralLinearGroup.map rationalAdele rational * binary) =
      integrand data test vector point parameter binary := by
  have characterValue : GodementIntegral.innerCharacter data parameter
      (GeneralLinearGroup.det (GeneralLinearGroup.map rationalAdele rational)) = 1 := by
    rw [GeneralLinearGroup.map_det]
    exact ThetaInvariance.innerCharacter_rational data parameter (GeneralLinearGroup.det rational)
  simp only [integrand, RectangularTheta.fullTheta_rational_binary, data.cusp.leftRational,
    map_mul, characterValue, one_mul]

theorem integrable_domain {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (fixed : vector.val ∈ fixedSubspace data.cusp finiteCongruence)
    (realTest : SchwartzMap RealSpace ℂ) (zeroValue : realTest 0 = 0) (zeroFourier : FourierTransform.fourier realTest 0 = 0)
    (finiteScale : FiniteAdelesˣ) (offset : FiniteRectangularFourier.Space) (point : AdelicGL) (parameter : ℂ) :
    IntegrableOn (integrand data (AdelicSchwartzTheta.tensorTest realTest (RectangularAdelicPoisson.finiteTest finiteScale offset)) vector point parameter)
      BinaryFundamentalDomain.domain BinaryHaar.measure := by
  obtain ⟨largePower, largePowerBound⟩ := exists_nat_gt (2 * WeightedAbsoluteTheta.exponent degree parameter)
  obtain ⟨smallPower, smallPowerBound⟩ := exists_nat_gt (-2 * WeightedAbsoluteTheta.exponent degree parameter)
  obtain ⟨cuspPower, cuspBound⟩ := exists_nat_gt (WeightedAbsoluteTheta.exponent degree parameter)
  obtain ⟨largeConstant, largeNonnegative, largeBound⟩ := large_log data vector fixed realTest zeroValue finiteScale offset point largePower cuspPower
  obtain ⟨smallConstant, smallNonnegative, smallBound⟩ := small_log data vector fixed realTest zeroFourier finiteScale offset point smallPower cuspPower
  let rate := min ((largePower : ℝ) - 2 * WeightedAbsoluteTheta.exponent degree parameter)
    (2 * WeightedAbsoluteTheta.exponent degree parameter - -(smallPower : ℝ))
  have ratePositive : 0 < rate := by
    apply lt_min
    · exact sub_pos.mpr largePowerBound
    · linarith
  apply ShellDecay.integrable_domain _
    (integrand_measurable data vector realTest _ (finiteTest_continuous finiteScale offset) (finiteTest_compactSupport finiteScale offset) point parameter)
    (rational_invariant data vector _ point parameter)
    ((largeConstant + smallConstant) * Real.exp (-WeightedAbsoluteTheta.exponent degree parameter * Real.log 2))
    rate ((cuspPower : ℝ) - WeightedAbsoluteTheta.exponent degree parameter) (by positivity) ratePositive (sub_pos.mpr cuspBound)
  intro integer natural shellParameter
  rw [norm_integrand data vector realTest zeroValue]
  simp only [SiegelShells.parameterize, height, SiegelChartFunctions.determinant_log_chart]
  have heightNonnegative : 0 ≤ (natural : ℝ) + shellParameter.2.2.1.val := add_nonneg (Nat.cast_nonneg _) shellParameter.2.2.1.property.1
  have horizontal : |shellParameter.2.2.2.1.val| ≤ 1 := abs_le.mpr shellParameter.2.2.2.1.property
  exact ExponentialWeights.two_rates _ largeConstant smallConstant largePower (-(smallPower : ℝ)) cuspPower (WeightedAbsoluteTheta.exponent degree parameter)
    ((integer : ℝ) + shellParameter.2.1.val) ((natural : ℝ) + shellParameter.2.2.1.val) (Real.log 2)
    largeNonnegative smallNonnegative
    (fun nonnegative => largeBound shellParameter.1 shellParameter.2.2.2.2 _ _ _ nonnegative heightNonnegative horizontal)
    (fun nonpositive => smallBound shellParameter.1 shellParameter.2.2.2.2 _ _ _ nonpositive heightNonnegative horizontal)

def total {degree : ℕ} (data : InducingData degree) (test : Rectangular Adeles → ℂ)
    (vector : data.cusp.smooth) (point : AdelicGL) (parameter : ℂ) : ℂ :=
  ∫ binary in BinaryFundamentalDomain.domain, integrand data test vector point parameter binary ∂BinaryHaar.measure

theorem differentiable {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (fixed : vector.val ∈ fixedSubspace data.cusp finiteCongruence)
    (realTest : SchwartzMap RealSpace ℂ) (zeroValue : realTest 0 = 0) (zeroFourier : FourierTransform.fourier realTest 0 = 0)
    (finiteScale : FiniteAdelesˣ) (offset : FiniteRectangularFourier.Space) (point : AdelicGL) :
    Differentiable ℂ (total data (AdelicSchwartzTheta.tensorTest realTest (RectangularAdelicPoisson.finiteTest finiteScale offset)) vector point) := by
  let test := AdelicSchwartzTheta.tensorTest realTest (RectangularAdelicPoisson.finiteTest finiteScale offset)
  have weightedIntegrable (exponent : ℝ) : IntegrableOn
      (fun binary => ‖integrand data test vector point 0 binary‖ * Real.exp (exponent * height binary))
      BinaryFundamentalDomain.domain BinaryHaar.measure := by
    have equality : (fun binary => ‖integrand data test vector point 0 binary‖ * Real.exp (exponent * height binary)) =
        fun binary => ‖integrand data test vector point (exponent : ℂ) binary‖ := by
      funext binary
      rw [integrand_eq_laplace data test vector point (exponent : ℂ), PositiveLaplaceIntegral.norm_integrand, Complex.ofReal_re]
    rw [equality]
    exact (integrable_domain data vector fixed realTest zeroValue zeroFourier finiteScale offset point (exponent : ℂ)).norm
  have equality : total data test vector point = fun parameter => ∫ binary in BinaryFundamentalDomain.domain,
      PositiveLaplaceIntegral.integrand (integrand data test vector point 0) height parameter binary ∂BinaryHaar.measure := by
    funext parameter
    exact integral_congr_ae (Eventually.of_forall (integrand_eq_laplace data test vector point parameter))
  change Differentiable ℂ (total data test vector point)
  rw [equality]
  exact PositiveLaplaceIntegral.differentiable_two_sided (BinaryHaar.measure.restrict BinaryFundamentalDomain.domain)
    (integrand data test vector point 0) height
    (integrand_measurable data vector realTest _ (finiteTest_continuous finiteScale offset) (finiteTest_compactSupport finiteScale offset) point 0)
    height_measurable weightedIntegrable

def continuation {degree : ℕ} (data : InducingData degree) (test : Rectangular Adeles → ℂ)
    (vector : data.cusp.smooth) (parameter : ℂ) (point : AdelicGL) : ℂ :=
  GodementIntegral.outerCharacter data parameter (GeneralLinearGroup.det point) * total data test vector point parameter

theorem outer_differentiable {degree : ℕ} (data : InducingData degree) (scalar : Adelesˣ) :
    Differentiable ℂ (fun parameter => GodementIntegral.outerCharacter data parameter scalar) := by
  change Differentiable ℂ (fun parameter => data.chi.toMonoidHom scalar *
    Complex.exp ((-2 * (1 / 2 + parameter / 3)) * (Real.log (adeleNorm scalar : ℝ) : ℂ)))
  fun_prop

theorem continuation_differentiable {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (fixed : vector.val ∈ fixedSubspace data.cusp finiteCongruence)
    (realTest : SchwartzMap RealSpace ℂ) (zeroValue : realTest 0 = 0) (zeroFourier : FourierTransform.fourier realTest 0 = 0)
    (finiteScale : FiniteAdelesˣ) (offset : FiniteRectangularFourier.Space) (point : AdelicGL) :
    Differentiable ℂ (fun parameter => continuation data
      (AdelicSchwartzTheta.tensorTest realTest (RectangularAdelicPoisson.finiteTest finiteScale offset)) vector parameter point) :=
  (outer_differentiable data _).mul (differentiable data vector fixed realTest zeroValue zeroFourier finiteScale offset point)

theorem eisenstein_hasSum {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (fixed : vector.val ∈ fixedSubspace data.cusp finiteCongruence)
    (realTest : SchwartzMap RealSpace ℂ) (finiteScale : FiniteAdelesˣ) (offset : FiniteRectangularFourier.Space)
    (point : AdelicGL) (parameter : ℂ) (halfPlane : (1 - (degree : ℝ)) / 2 < parameter.re) :
    HasSum (fun flag => eisensteinSummand (GodementIntegral.sectionFunction data
      (AdelicSchwartzTheta.tensorTest realTest (RectangularAdelicPoisson.finiteTest finiteScale offset)) vector) parameter point flag)
      (continuation data (AdelicSchwartzTheta.tensorTest realTest (RectangularAdelicPoisson.finiteTest finiteScale offset)) vector parameter point) :=
  NonzeroGodementUnfolding.eisenstein_hasSum data vector fixed realTest _ (finiteTest_continuous finiteScale offset)
    (finiteTest_compactSupport finiteScale offset) parameter point halfPlane

theorem isEisensteinContinuation {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (fixed : vector.val ∈ fixedSubspace data.cusp finiteCongruence)
    (realTest : SchwartzMap RealSpace ℂ) (zeroValue : realTest 0 = 0) (zeroFourier : FourierTransform.fourier realTest 0 = 0)
    (finiteScale : FiniteAdelesˣ) (offset : FiniteRectangularFourier.Space) :
    IsEisensteinContinuation
      (GodementIntegral.sectionFunction data (AdelicSchwartzTheta.tensorTest realTest (RectangularAdelicPoisson.finiteTest finiteScale offset)) vector)
      (continuation data (AdelicSchwartzTheta.tensorTest realTest (RectangularAdelicPoisson.finiteTest finiteScale offset)) vector) := by
  refine ⟨fun point parameter =>
    ((continuation_differentiable data vector fixed realTest zeroValue zeroFourier finiteScale offset point).analyticAt parameter).meromorphicAt,
    (1 - (degree : ℝ)) / 2, ?_⟩
  intro parameter halfPlane point
  exact eisenstein_hasSum data vector fixed realTest finiteScale offset point parameter halfPlane

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.ZeroConstantThetaIntegral
