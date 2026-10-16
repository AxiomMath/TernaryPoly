module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Godement.QuotientIntegrability
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.PeriodizedIntegrability

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularKernel
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.GodementIntegral TernaryPeriodPolynomials.PlaneEisensteinContinuation.GodementUnfolding TernaryPeriodPolynomials.PlaneEisensteinContinuation.GodementAbsolute
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel
open scoped TernaryPeriodPolynomials.PlaneEisensteinContinuation.GodementUnfolding

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.RawGodementIntegrability

theorem exponent_eq (degree : ℕ) (parameter : ℂ) :
    WeightedAbsoluteTheta.exponent degree parameter = (degree : ℝ) / 2 + 3 + parameter.re := by
  simp [WeightedAbsoluteTheta.exponent, binaryInductionExponent, inductionExponent]
  ring

theorem halfPlane_iff (degree : ℕ) (parameter : ℂ) :
    7 < 2 * WeightedAbsoluteTheta.exponent degree parameter ↔ (1 - (degree : ℝ)) / 2 < parameter.re := by
  rw [exponent_eq]
  constructor <;> intro bound <;> linarith

theorem raw_measurable {degree : ℕ} (data : InducingData degree) (test : Rectangular Adeles → ℂ)
    (continuousTest : Continuous test) (vector : data.cusp.smooth) (parameter : ℂ) (point : AdelicGL) :
    Measurable (rawKernel data test vector parameter point) := by
  have kernelContinuous : Continuous (kernel test point) :=
    continuousTest.comp (continuous_const.matrix_mul (Units.continuous_val (M := Matrix (Fin 2) (Fin 2) Adeles)))
  exact (kernelContinuous.measurable.mul ((AdelicNormMeasurable.innerCharacter_measurable data parameter).comp
    WeightedAbsoluteTheta.determinant_continuous.measurable)).mul (CuspFunctionContinuity.continuous data.cusp vector).measurable

theorem flag_injective (flag : Flags .plane) :
    Function.Injective (fun rational : BinaryRationalGL => FrameUnfolding.parameterize (flag, rational)) := by
  intro first second equality
  exact (Prod.mk.inj (FrameUnfolding.parameterize_injective equality)).2

theorem translates_summable {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (realTest : SchwartzMap RealSpace ℂ) (finiteTest : Rectangular FiniteAdeles → ℂ)
    (finiteContinuous : Continuous finiteTest) (finiteSupport : HasCompactSupport finiteTest)
    (parameter : ℂ) (point : AdelicGL) (flag : Flags .plane) (binary : BinaryAdelicGL) :
    Summable (fun rational : BinaryRationalGL =>
      ‖rawKernel data (AdelicSchwartzTheta.tensorTest realTest finiteTest) vector parameter
        (rationalGroup flag.out⁻¹ * point) (rational • binary)‖) := by
  have result : Summable (fun rational : BinaryRationalGL =>
      ‖weightedTerm data (AdelicSchwartzTheta.tensorTest realTest finiteTest) vector parameter point
        (FrameUnfolding.parameterize (flag, rational)) binary‖) :=
    (GodementQuotientIntegrability.norm_summable data vector realTest finiteTest finiteContinuous finiteSupport parameter point binary).comp_injective
      (flag_injective flag)
  apply result.congr
  intro rational
  exact congrArg norm (weightedTerm_parameterize data _ vector parameter point flag rational binary)

theorem translates_bound {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (realTest : SchwartzMap RealSpace ℂ) (finiteTest : Rectangular FiniteAdeles → ℂ)
    (finiteContinuous : Continuous finiteTest) (finiteSupport : HasCompactSupport finiteTest)
    (parameter : ℂ) (point : AdelicGL) (flag : Flags .plane) (binary : BinaryAdelicGL) :
    (∑' rational : BinaryRationalGL,
      ‖rawKernel data (AdelicSchwartzTheta.tensorTest realTest finiteTest) vector parameter
        (rationalGroup flag.out⁻¹ * point) (rational • binary)‖) ≤
      ∑' frame, ‖weightedTerm data (AdelicSchwartzTheta.tensorTest realTest finiteTest) vector parameter point frame binary‖ := by
  apply Summable.tsum_le_tsum_of_inj (fun rational => FrameUnfolding.parameterize (flag, rational)) (flag_injective flag)
    (fun _ _ => norm_nonneg _) (fun rational => ?_)
    (translates_summable data vector realTest finiteTest finiteContinuous finiteSupport parameter point flag binary)
    (GodementQuotientIntegrability.norm_summable data vector realTest finiteTest finiteContinuous finiteSupport parameter point binary)
  rw [weightedTerm_parameterize]
  rfl

theorem raw_integrable {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (fixed : vector.val ∈ fixedSubspace data.cusp finiteCongruence)
    (realTest : SchwartzMap RealSpace ℂ) (finiteTest : Rectangular FiniteAdeles → ℂ)
    (finiteContinuous : Continuous finiteTest) (finiteSupport : HasCompactSupport finiteTest)
    (parameter : ℂ) (point : AdelicGL) (halfPlane : 7 < 2 * WeightedAbsoluteTheta.exponent degree parameter) (flag : Flags .plane) :
    Integrable (rawKernel data (AdelicSchwartzTheta.tensorTest realTest finiteTest) vector parameter
      (rationalGroup flag.out⁻¹ * point)) BinaryHaar.measure :=
  PeriodizedIntegrability.integrable BinaryHaar.measure BinaryFundamentalDomain.domain BinaryFundamentalDomain.domain_fundamental _
    (raw_measurable data _ (AdelicSchwartzTheta.tensorTest_continuous realTest finiteTest finiteContinuous) vector parameter _)
    _ (GodementQuotientIntegrability.sum_norm_integrable data vector fixed realTest finiteTest finiteContinuous finiteSupport parameter point halfPlane)
    (translates_summable data vector realTest finiteTest finiteContinuous finiteSupport parameter point flag)
    (translates_bound data vector realTest finiteTest finiteContinuous finiteSupport parameter point flag)

theorem raw_integral_norm_summable {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (fixed : vector.val ∈ fixedSubspace data.cusp finiteCongruence)
    (realTest : SchwartzMap RealSpace ℂ) (finiteTest : Rectangular FiniteAdeles → ℂ)
    (finiteContinuous : Continuous finiteTest) (finiteSupport : HasCompactSupport finiteTest)
    (parameter : ℂ) (point : AdelicGL) (halfPlane : 7 < 2 * WeightedAbsoluteTheta.exponent degree parameter) :
    Summable (fun flag : Flags .plane => ∫ binary,
      ‖rawKernel data (AdelicSchwartzTheta.tensorTest realTest finiteTest) vector parameter
        (rationalGroup flag.out⁻¹ * point) binary‖ ∂BinaryHaar.measure) :=
  (GodementAbsolute.absolute_iff data _ vector parameter point
    (raw_integrable data vector fixed realTest finiteTest finiteContinuous finiteSupport parameter point halfPlane)).mp
      (GodementQuotientIntegrability.integral_norm_summable data vector fixed realTest finiteTest finiteContinuous finiteSupport parameter point halfPlane)

theorem eisenstein_hasSum {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (fixed : vector.val ∈ fixedSubspace data.cusp finiteCongruence)
    (realTest : SchwartzMap RealSpace ℂ) (finiteTest : Rectangular FiniteAdeles → ℂ)
    (finiteContinuous : Continuous finiteTest) (finiteSupport : HasCompactSupport finiteTest)
    (parameter : ℂ) (point : AdelicGL) (halfPlane : 7 < 2 * WeightedAbsoluteTheta.exponent degree parameter) :
    HasSum (fun flag => eisensteinSummand (sectionFunction data (AdelicSchwartzTheta.tensorTest realTest finiteTest) vector) parameter point flag)
      (outerCharacter data parameter (GeneralLinearGroup.det point) *
        ∫ binary in BinaryFundamentalDomain.domain,
          ThetaInvariance.integrand data (AdelicSchwartzTheta.tensorTest realTest finiteTest) vector parameter point binary ∂BinaryHaar.measure) :=
  GodementAbsolute.eisenstein_hasSum data _ vector parameter point
    (raw_integrable data vector fixed realTest finiteTest finiteContinuous finiteSupport parameter point halfPlane)
    (raw_integral_norm_summable data vector fixed realTest finiteTest finiteContinuous finiteSupport parameter point halfPlane)

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.RawGodementIntegrability
