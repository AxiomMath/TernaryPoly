module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Vector.ThetaDecay
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.ZeroConstantThetaIntegral

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory Filter
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz TernaryPeriodPolynomials.PlaneEisensteinContinuation.VectorThetaDecay
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.SobolevSeminorms TernaryPeriodPolynomials.PlaneEisensteinContinuation.LargeThetaIntegral
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.ZeroConstantThetaDecay

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.VectorThetaIntegral

variable {Source : Type*} [NormedAddCommGroup Source] [NormedSpace ℂ Source] [CompleteSpace Source]

omit [NormedAddCommGroup Source] [NormedSpace ℂ Source] [CompleteSpace Source] in
theorem matrixTerm_rational_binary (test : Rectangular Adeles → Source) (point : AdelicGL)
    (binary : BinaryAdelicGL) (rational : BinaryRationalGL) (matrix : Rectangular ℚ) :
    BanachAdelicTheta.matrixTerm test point (GeneralLinearGroup.map rationalAdele rational * binary) matrix =
      BanachAdelicTheta.matrixTerm test point binary (RectangularTheta.rightEquiv rational matrix) := by
  unfold BanachAdelicTheta.matrixTerm
  change test (point⁻¹.val * matrix.map rationalAdele *
      (GeneralLinearGroup.map rationalAdele rational * binary).val) =
    test (point⁻¹.val * (matrix * rational.val).map rationalAdele * binary.val)
  rw [Units.val_mul, Matrix.map_mul]
  simp only [Matrix.mul_assoc]
  rfl

omit [NormedSpace ℂ Source] [CompleteSpace Source] in
theorem theta_rational_binary (test : Rectangular Adeles → Source) (point : AdelicGL)
    (binary : BinaryAdelicGL) (rational : BinaryRationalGL) :
    BanachAdelicTheta.fullTheta test point (GeneralLinearGroup.map rationalAdele rational * binary) =
      BanachAdelicTheta.fullTheta test point binary := by
  simp only [BanachAdelicTheta.fullTheta, matrixTerm_rational_binary]
  exact (RectangularTheta.rightEquiv rational).tsum_eq _

def integrand {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (test : Rectangular Adeles → Source) (point : AdelicGL) (parameter : ℂ) (binary : BinaryAdelicGL) : ℂ :=
  GodementIntegral.innerCharacter data parameter (GeneralLinearGroup.det binary) *
    VectorTheta.fullTheta data family test point binary

omit [CompleteSpace Source] in
theorem rational_invariant {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (test : Rectangular Adeles → Source) (point : AdelicGL) (parameter : ℂ)
    (rational : BinaryRationalGL) (binary : BinaryAdelicGL) :
    integrand data family test point parameter (GeneralLinearGroup.map rationalAdele rational * binary) =
      integrand data family test point parameter binary := by
  have characterValue : GodementIntegral.innerCharacter data parameter
      (GeneralLinearGroup.det (GeneralLinearGroup.map rationalAdele rational)) = 1 := by
    rw [GeneralLinearGroup.map_det]
    exact ThetaInvariance.innerCharacter_rational data parameter (GeneralLinearGroup.det rational)
  simp only [integrand, VectorTheta.fullTheta, theta_rational_binary, data.cusp.leftRational,
    map_mul, characterValue, one_mul]

omit [CompleteSpace Source] in
theorem norm_integrand {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (test : Rectangular Adeles → Source) (point : AdelicGL) (parameter : ℂ) (binary : BinaryAdelicGL) :
    ‖integrand data family test point parameter binary‖ =
      Real.exp (WeightedAbsoluteTheta.exponent degree parameter * height binary) *
        ‖VectorTheta.fullTheta data family test point binary‖ := by
  rw [integrand, norm_mul, WeightedAbsoluteTheta.inner_norm]
  rfl

omit [CompleteSpace Source] in
theorem integrand_eq_laplace {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (test : Rectangular Adeles → Source) (point : AdelicGL) (parameter : ℂ) (binary : BinaryAdelicGL) :
    integrand data family test point parameter binary =
      PositiveLaplaceIntegral.integrand (integrand data family test point 0) height parameter binary := by
  unfold integrand PositiveLaplaceIntegral.integrand height
  rw [character_factor data parameter]
  ring

theorem integrand_measurable {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (continuous : Continuous (fun vector => (family vector).val.val))
    (realTest : SchwartzMap RealSpace Source) (finiteTest : Rectangular FiniteAdeles → ℂ)
    (finiteContinuous : Continuous finiteTest) (finiteSupport : HasCompactSupport finiteTest)
    (point : AdelicGL) (parameter : ℂ) :
    Measurable (integrand data family (BanachAdelicTheta.tensorTest realTest finiteTest) point parameter) := by
  have thetaContinuous : Continuous (fun binary => VectorTheta.fullTheta data family
      (BanachAdelicTheta.tensorTest realTest finiteTest) point binary) :=
    (VectorTheta.fullTheta_continuous data family continuous realTest finiteTest finiteContinuous finiteSupport).comp
      (f := fun binary : BinaryAdelicGL => (point, binary))
      (continuous_const.prodMk (continuous_id : Continuous (fun binary : BinaryAdelicGL => binary)))
  exact ((AdelicNormMeasurable.innerCharacter_measurable data parameter).comp
    WeightedAbsoluteTheta.determinant_continuous.measurable).mul thetaContinuous.measurable

theorem integrable_domain {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (continuous : Continuous (fun vector => (family vector).val.val))
    (realTest : SchwartzMap RealSpace Source) (zeroValue : realTest 0 = 0) (zeroFourier : FourierTransform.fourier realTest 0 = 0)
    (finiteScale : FiniteAdelesˣ) (offset : FiniteRectangularFourier.Space) (point : AdelicGL) (parameter : ℂ) :
    IntegrableOn (integrand data family (BanachAdelicTheta.tensorTest realTest (RectangularAdelicPoisson.finiteTest finiteScale offset)) point parameter)
      BinaryFundamentalDomain.domain BinaryHaar.measure := by
  obtain ⟨largePower, largePowerBound⟩ := exists_nat_gt (2 * WeightedAbsoluteTheta.exponent degree parameter)
  obtain ⟨smallPower, smallPowerBound⟩ := exists_nat_gt (-2 * WeightedAbsoluteTheta.exponent degree parameter)
  obtain ⟨cuspPower, cuspBound⟩ := exists_nat_gt (WeightedAbsoluteTheta.exponent degree parameter)
  obtain ⟨largeConstant, largeNonnegative, largeBound⟩ := VectorThetaDecay.large_log data family continuous realTest zeroValue finiteScale offset point largePower cuspPower
  obtain ⟨smallConstant, smallNonnegative, smallBound⟩ := VectorThetaDecay.small_log data family continuous realTest zeroFourier finiteScale offset point smallPower cuspPower
  let rate := min ((largePower : ℝ) - 2 * WeightedAbsoluteTheta.exponent degree parameter)
    (2 * WeightedAbsoluteTheta.exponent degree parameter - -(smallPower : ℝ))
  have ratePositive : 0 < rate := by
    apply lt_min
    · exact sub_pos.mpr largePowerBound
    · linarith
  apply ShellDecay.integrable_domain _
    (integrand_measurable data family continuous realTest _ (finiteTest_continuous finiteScale offset) (finiteTest_compactSupport finiteScale offset) point parameter)
    (rational_invariant data family _ point parameter)
    ((largeConstant + smallConstant) * Real.exp (-WeightedAbsoluteTheta.exponent degree parameter * Real.log 2))
    rate ((cuspPower : ℝ) - WeightedAbsoluteTheta.exponent degree parameter) (by positivity) ratePositive (sub_pos.mpr cuspBound)
  intro integer natural shellParameter
  rw [norm_integrand]
  simp only [SiegelShells.parameterize, height, SiegelChartFunctions.determinant_log_chart]
  have heightNonnegative : 0 ≤ (natural : ℝ) + shellParameter.2.2.1.val := add_nonneg (Nat.cast_nonneg _) shellParameter.2.2.1.property.1
  have horizontal : |shellParameter.2.2.2.1.val| ≤ 1 := abs_le.mpr shellParameter.2.2.2.1.property
  exact ExponentialWeights.two_rates _ largeConstant smallConstant largePower (-(smallPower : ℝ)) cuspPower (WeightedAbsoluteTheta.exponent degree parameter)
    ((integer : ℝ) + shellParameter.2.1.val) ((natural : ℝ) + shellParameter.2.2.1.val) (Real.log 2)
    largeNonnegative smallNonnegative
    (fun nonnegative => largeBound shellParameter.1 shellParameter.2.2.2.2 _ _ _ nonnegative heightNonnegative horizontal)
    (fun nonpositive => smallBound shellParameter.1 shellParameter.2.2.2.2 _ _ _ nonpositive heightNonnegative horizontal)

def total {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (test : Rectangular Adeles → Source) (point : AdelicGL) (parameter : ℂ) : ℂ :=
  ∫ binary in BinaryFundamentalDomain.domain, integrand data family test point parameter binary ∂BinaryHaar.measure

theorem differentiable {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (continuous : Continuous (fun vector => (family vector).val.val))
    (realTest : SchwartzMap RealSpace Source) (zeroValue : realTest 0 = 0) (zeroFourier : FourierTransform.fourier realTest 0 = 0)
    (finiteScale : FiniteAdelesˣ) (offset : FiniteRectangularFourier.Space) (point : AdelicGL) :
    Differentiable ℂ (total data family (BanachAdelicTheta.tensorTest realTest (RectangularAdelicPoisson.finiteTest finiteScale offset)) point) := by
  let test := BanachAdelicTheta.tensorTest realTest (RectangularAdelicPoisson.finiteTest finiteScale offset)
  have weightedIntegrable (exponent : ℝ) : IntegrableOn
      (fun binary => ‖integrand data family test point 0 binary‖ * Real.exp (exponent * height binary))
      BinaryFundamentalDomain.domain BinaryHaar.measure := by
    have equality : (fun binary => ‖integrand data family test point 0 binary‖ * Real.exp (exponent * height binary)) =
        fun binary => ‖integrand data family test point (exponent : ℂ) binary‖ := by
      funext binary
      rw [integrand_eq_laplace data family test point (exponent : ℂ), PositiveLaplaceIntegral.norm_integrand, Complex.ofReal_re]
    rw [equality]
    exact (integrable_domain data family continuous realTest zeroValue zeroFourier finiteScale offset point (exponent : ℂ)).norm
  have equality : total data family test point = fun parameter => ∫ binary in BinaryFundamentalDomain.domain,
      PositiveLaplaceIntegral.integrand (integrand data family test point 0) height parameter binary ∂BinaryHaar.measure := by
    funext parameter
    exact integral_congr_ae (Eventually.of_forall (integrand_eq_laplace data family test point parameter))
  change Differentiable ℂ (total data family test point)
  rw [equality]
  exact PositiveLaplaceIntegral.differentiable_two_sided (BinaryHaar.measure.restrict BinaryFundamentalDomain.domain)
    (integrand data family test point 0) height
    (integrand_measurable data family continuous realTest _ (finiteTest_continuous finiteScale offset) (finiteTest_compactSupport finiteScale offset) point 0)
    height_measurable weightedIntegrable

def continuation {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (test : Rectangular Adeles → Source) (parameter : ℂ) (point : AdelicGL) : ℂ :=
  GodementIntegral.outerCharacter data parameter (GeneralLinearGroup.det point) * total data family test point parameter

theorem continuation_differentiable {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (continuous : Continuous (fun vector => (family vector).val.val))
    (realTest : SchwartzMap RealSpace Source) (zeroValue : realTest 0 = 0) (zeroFourier : FourierTransform.fourier realTest 0 = 0)
    (finiteScale : FiniteAdelesˣ) (offset : FiniteRectangularFourier.Space) (point : AdelicGL) :
    Differentiable ℂ (fun parameter => continuation data family
      (BanachAdelicTheta.tensorTest realTest (RectangularAdelicPoisson.finiteTest finiteScale offset)) parameter point) :=
  (ZeroConstantThetaIntegral.outer_differentiable data _).mul
    (differentiable data family continuous realTest zeroValue zeroFourier finiteScale offset point)

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.VectorThetaIntegral
