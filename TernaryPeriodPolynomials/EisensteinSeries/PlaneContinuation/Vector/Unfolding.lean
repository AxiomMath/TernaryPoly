module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Vector.SingularTheta

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularKernel
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.SobolevSeminorms TernaryPeriodPolynomials.PlaneEisensteinContinuation.VectorMatrixOrbit
open scoped TernaryPeriodPolynomials.PlaneEisensteinContinuation.GodementUnfolding

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.VectorUnfolding

variable {Source : Type*} [NormedAddCommGroup Source] [NormedSpace ℂ Source] [CompleteSpace Source]

omit [CompleteSpace Source] in
theorem term_parameterize {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (test : Rectangular Adeles → Source) (parameter : ℂ) (point : AdelicGL)
    (flag : Flags .plane) (rational : BinaryRationalGL) (binary : BinaryAdelicGL) :
    VectorMatrixOrbit.term data family test parameter point (FrameUnfolding.parameterize (flag, rational)).val binary =
      VectorGodement.integrand data (liftTest data family test) parameter (rationalGroup flag.out⁻¹ * point) (rational • binary) := by
  have argument : point⁻¹.val * (FrameUnfolding.parameterize (flag, rational)).val.map rationalAdele * binary.val =
      FrameProfile.frame (rationalGroup flag.out⁻¹ * point) * (rational • binary).val := by
    rw [FrameUnfolding.parameterize_val, Matrix.map_mul, columns_map, FrameProfile.frame,
      _root_.mul_inv_rev, ← map_inv, inv_inv, Units.val_mul, GodementUnfolding.rational_smul, Units.val_mul]
    change point⁻¹.val * (columns (rationalGroup flag.out).val *
        (GeneralLinearGroup.map rationalAdele rational).val) * binary.val = _
    rw [← mul_standard (rationalGroup flag.out).val]
    simp only [standard, Matrix.mul_assoc]
  have characterValue : GodementIntegral.innerCharacter data parameter
      (GeneralLinearGroup.det (GeneralLinearGroup.map rationalAdele rational)) = 1 := by
    rw [GeneralLinearGroup.map_det]
    exact ThetaInvariance.innerCharacter_rational data parameter (GeneralLinearGroup.det rational)
  simp only [VectorMatrixOrbit.term, VectorTheta.term, BanachAdelicTheta.matrixTerm, argument,
    VectorGodement.integrand, liftTest, GodementUnfolding.rational_smul, map_mul, characterValue,
    one_mul, data.cusp.leftRational]

omit [CompleteSpace Source] in
theorem raw_eq_term {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (test : Rectangular Adeles → Source) (parameter : ℂ) (point : AdelicGL) :
    VectorGodement.integrand data (liftTest data family test) parameter point =
      VectorMatrixOrbit.term data family test parameter point standard := by
  funext binary
  simp only [VectorGodement.integrand, VectorMatrixOrbit.term, VectorTheta.term,
    BanachAdelicTheta.matrixTerm, standard_map, FrameProfile.frame, liftTest]

theorem raw_measurable {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (continuous : Continuous (fun vector => (family vector).val.val))
    (test : Rectangular Adeles → Source) (testContinuous : Continuous test) (parameter : ℂ) (point : AdelicGL) :
    Measurable (VectorGodement.integrand data (liftTest data family test) parameter point) := by
  rw [raw_eq_term]
  exact term_measurable data family continuous test testContinuous parameter point standard

theorem raw_integrable {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (continuous : Continuous (fun vector => (family vector).val.val))
    (realTest : SchwartzMap RealSpace Source) (finiteTest : Rectangular FiniteAdeles → ℂ)
    (finiteContinuous : Continuous finiteTest) (finiteSupport : HasCompactSupport finiteTest)
    (parameter : ℂ) (point : AdelicGL) (halfPlane : 7 < 2 * WeightedAbsoluteTheta.exponent degree parameter) (flag : Flags .plane) :
    Integrable (VectorGodement.integrand data (liftTest data family (BanachAdelicTheta.tensorTest realTest finiteTest))
      parameter (rationalGroup flag.out⁻¹ * point)) BinaryHaar.measure := by
  let index : BinaryRationalGL → Rectangular ℚ := fun rational => (FrameUnfolding.parameterize (flag, rational)).val
  have injective : Function.Injective index := Subtype.val_injective.comp (RawGodementIntegrability.flag_injective flag)
  have nonzero : ∀ rational, index rational ≠ 0 := fun rational =>
    GodementQuotientIntegrability.frame_nonzero (FrameUnfolding.parameterize (flag, rational))
  apply PeriodizedIntegrability.integrable BinaryHaar.measure BinaryFundamentalDomain.domain BinaryFundamentalDomain.domain_fundamental _
    (raw_measurable data family continuous _ (BanachAdelicTheta.tensorTest_continuous realTest finiteTest finiteContinuous) parameter _)
    _ (VectorAbsoluteThetaDecay.integrable_domain data family continuous realTest finiteTest finiteContinuous finiteSupport parameter point halfPlane).norm
  · intro binary
    simpa only [index, term_parameterize] using VectorMatrixSeries.norm_summable data family continuous realTest finiteTest
      finiteContinuous finiteSupport parameter point binary index injective
  · intro binary
    simpa only [index, term_parameterize] using VectorMatrixSeries.sum_norm_bound data family continuous realTest finiteTest
      finiteContinuous finiteSupport parameter point binary index injective nonzero

theorem raw_integrable_at {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (continuous : Continuous (fun vector => (family vector).val.val))
    (realTest : SchwartzMap RealSpace Source) (finiteTest : Rectangular FiniteAdeles → ℂ)
    (finiteContinuous : Continuous finiteTest) (finiteSupport : HasCompactSupport finiteTest)
    (parameter : ℂ) (point : AdelicGL) (halfPlane : (1 - (degree : ℝ)) / 2 < parameter.re) :
    Integrable (VectorGodement.integrand data (liftTest data family (BanachAdelicTheta.tensorTest realTest finiteTest))
      parameter point) BinaryHaar.measure := by
  let flag : Flags .plane := QuotientGroup.mk 1
  have result := raw_integrable data family continuous realTest finiteTest finiteContinuous finiteSupport
    parameter (rationalGroup flag.out * point) ((RawGodementIntegrability.halfPlane_iff degree parameter).mpr halfPlane) flag
  simpa only [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul] using result

theorem raw_hasSum {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (continuous : Continuous (fun vector => (family vector).val.val))
    (realTest : SchwartzMap RealSpace Source) (finiteTest : Rectangular FiniteAdeles → ℂ)
    (finiteContinuous : Continuous finiteTest) (finiteSupport : HasCompactSupport finiteTest)
    (parameter : ℂ) (point : AdelicGL) (halfPlane : 7 < 2 * WeightedAbsoluteTheta.exponent degree parameter) (flag : Flags .plane) :
    HasSum (fun rational : BinaryRationalGL => ∫ binary in BinaryFundamentalDomain.domain,
      VectorMatrixOrbit.term data family (BanachAdelicTheta.tensorTest realTest finiteTest) parameter point
        (FrameUnfolding.parameterize (flag, rational)).val binary ∂BinaryHaar.measure)
      (∫ binary, VectorGodement.integrand data (liftTest data family (BanachAdelicTheta.tensorTest realTest finiteTest))
        parameter (rationalGroup flag.out⁻¹ * point) binary ∂BinaryHaar.measure) := by
  simpa only [term_parameterize] using FundamentalIntegration.hasSum_translates BinaryFundamentalDomain.domain_fundamental
    (raw_integrable data family continuous realTest finiteTest finiteContinuous finiteSupport parameter point halfPlane flag)

theorem eisenstein_frame_hasSum {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (continuous : Continuous (fun vector => (family vector).val.val))
    (realTest : SchwartzMap RealSpace Source) (finiteTest : Rectangular FiniteAdeles → ℂ)
    (finiteContinuous : Continuous finiteTest) (finiteSupport : HasCompactSupport finiteTest)
    (parameter : ℂ) (point : AdelicGL) (halfPlane : 7 < 2 * WeightedAbsoluteTheta.exponent degree parameter) :
    HasSum (fun flag => eisensteinSummand (VectorGodement.sectionFunction data
      (liftTest data family (BanachAdelicTheta.tensorTest realTest finiteTest))) parameter point flag)
      (GodementIntegral.outerCharacter data parameter (GeneralLinearGroup.det point) *
        ∫ binary in BinaryFundamentalDomain.domain,
          ∑' matrix : Frame, VectorMatrixOrbit.term data family (BanachAdelicTheta.tensorTest realTest finiteTest)
            parameter point matrix.val binary ∂BinaryHaar.measure) := by
  have frameSum := VectorMatrixSeries.hasSum_integral data family continuous realTest finiteTest finiteContinuous finiteSupport
    parameter point halfPlane (Subtype.val : Frame → Rectangular ℚ) Subtype.val_injective GodementQuotientIntegrability.frame_nonzero
  have pairSum := (FrameUnfolding.hasSum_iff _ _).mp frameSum
  have flagSum := pairSum.prod_fiberwise (raw_hasSum data family continuous realTest finiteTest finiteContinuous finiteSupport parameter point halfPlane)
  simpa only [eisensteinSummand, VectorGodement.sectionFunction, GodementUnfolding.outer_rational_left] using
    flagSum.mul_left (GodementIntegral.outerCharacter data parameter (GeneralLinearGroup.det point))

theorem eisenstein_hasSum {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (continuous : Continuous (fun vector => (family vector).val.val))
    (realTest : SchwartzMap RealSpace Source) (zero : realTest 0 = 0) (finiteTest : Rectangular FiniteAdeles → ℂ)
    (finiteContinuous : Continuous finiteTest) (finiteSupport : HasCompactSupport finiteTest)
    (parameter : ℂ) (point : AdelicGL) (halfPlane : (1 - (degree : ℝ)) / 2 < parameter.re) :
    HasSum (fun flag => eisensteinSummand (VectorGodement.sectionFunction data
      (liftTest data family (BanachAdelicTheta.tensorTest realTest finiteTest))) parameter point flag)
      (VectorThetaIntegral.continuation data family (BanachAdelicTheta.tensorTest realTest finiteTest) parameter point) := by
  have bound := (RawGodementIntegrability.halfPlane_iff degree parameter).mpr halfPlane
  have result := eisenstein_frame_hasSum data family continuous realTest finiteTest finiteContinuous finiteSupport parameter point bound
  rw [← VectorSingularTheta.integral_eq_frame data family continuous realTest zero finiteTest finiteContinuous finiteSupport parameter point bound] at result
  exact result

theorem isEisensteinContinuation {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (continuous : Continuous (fun vector => (family vector).val.val))
    (realTest : SchwartzMap RealSpace Source) (zero : realTest 0 = 0) (zeroFourier : FourierTransform.fourier realTest 0 = 0)
    (finiteScale : FiniteAdelesˣ) (offset : FiniteRectangularFourier.Space) :
    IsEisensteinContinuation
      (VectorGodement.sectionFunction data (liftTest data family
        (BanachAdelicTheta.tensorTest realTest (RectangularAdelicPoisson.finiteTest finiteScale offset))))
      (VectorThetaIntegral.continuation data family
        (BanachAdelicTheta.tensorTest realTest (RectangularAdelicPoisson.finiteTest finiteScale offset))) := by
  refine ⟨fun point parameter =>
    ((VectorThetaIntegral.continuation_differentiable data family continuous realTest zero zeroFourier finiteScale offset point).analyticAt parameter).meromorphicAt,
    (1 - (degree : ℝ)) / 2, ?_⟩
  intro parameter halfPlane point
  exact eisenstein_hasSum data family continuous realTest zero _ (ZeroConstantThetaDecay.finiteTest_continuous finiteScale offset)
    (ZeroConstantThetaDecay.finiteTest_compactSupport finiteScale offset) parameter point halfPlane

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.VectorUnfolding
