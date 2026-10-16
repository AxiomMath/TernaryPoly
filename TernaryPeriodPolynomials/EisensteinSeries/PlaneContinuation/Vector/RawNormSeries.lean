module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Vector.Unfolding

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.SobolevSeminorms TernaryPeriodPolynomials.PlaneEisensteinContinuation.VectorMatrixOrbit
open scoped TernaryPeriodPolynomials.PlaneEisensteinContinuation.GodementUnfolding

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.VectorRawNormSeries

variable {Source : Type} [NormedAddCommGroup Source] [NormedSpace ℂ Source] [CompleteSpace Source]
variable {degree : ℕ} (data : InducingData degree)
variable (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
variable (continuous : Continuous (fun vector => (family vector).val.val))
variable (realTest : SchwartzMap RealSpace Source) (finiteTest : Rectangular FiniteAdeles → ℂ)
variable (finiteContinuous : Continuous finiteTest) (finiteSupport : HasCompactSupport finiteTest)
variable (parameter : ℂ) (point : AdelicGL) (halfPlane : 7 < 2 * WeightedAbsoluteTheta.exponent degree parameter)

include continuous finiteContinuous finiteSupport halfPlane

theorem fiber_hasSum (flag : Flags .plane) :
    HasSum (fun rational : BinaryRationalGL => ∫ binary in BinaryFundamentalDomain.domain,
      ‖term data family (BanachAdelicTheta.tensorTest realTest finiteTest) parameter point
        (FrameUnfolding.parameterize (flag, rational)).val binary‖ ∂BinaryHaar.measure)
      (∫ binary, ‖VectorGodement.integrand data (liftTest data family (BanachAdelicTheta.tensorTest realTest finiteTest))
        parameter (rationalGroup flag.out⁻¹ * point) binary‖ ∂BinaryHaar.measure) := by
  simpa only [VectorUnfolding.term_parameterize] using
    FundamentalIntegration.hasSum_norm_translates BinaryFundamentalDomain.domain_fundamental
      (VectorUnfolding.raw_integrable data family continuous realTest finiteTest finiteContinuous finiteSupport
        parameter point halfPlane flag)

theorem hasSum :
    HasSum (fun flag : Flags .plane => ∫ binary,
      ‖VectorGodement.integrand data (liftTest data family (BanachAdelicTheta.tensorTest realTest finiteTest))
        parameter (rationalGroup flag.out⁻¹ * point) binary‖ ∂BinaryHaar.measure)
      (∫ binary in BinaryFundamentalDomain.domain, ∑' matrix : Frame,
        ‖term data family (BanachAdelicTheta.tensorTest realTest finiteTest) parameter point matrix.val binary‖ ∂BinaryHaar.measure) := by
  let _ : Countable (Rectangular ℚ) := inferInstanceAs (Countable (Fin 3 → Fin 2 → ℚ))
  have normSummable := VectorMatrixSeries.integral_norm_summable data family continuous realTest finiteTest
    finiteContinuous finiteSupport parameter point halfPlane (Subtype.val : Frame → Rectangular ℚ)
    Subtype.val_injective GodementQuotientIntegrability.frame_nonzero
  have frameSum := hasSum_integral_of_summable_integral_norm
    (fun matrix : Frame => (VectorMatrixSeries.term_integrable data family continuous realTest finiteTest
      finiteContinuous finiteSupport parameter point halfPlane (Subtype.val : Frame → Rectangular ℚ)
      Subtype.val_injective GodementQuotientIntegrability.frame_nonzero matrix).norm)
    (by simpa only [norm_norm] using normSummable)
  exact ((FrameUnfolding.hasSum_iff _ _).mp frameSum).prod_fiberwise
    (fiber_hasSum data family continuous realTest finiteTest finiteContinuous finiteSupport parameter point halfPlane)

theorem sum_bound :
    (∑' flag : Flags .plane, ∫ binary,
      ‖VectorGodement.integrand data (liftTest data family (BanachAdelicTheta.tensorTest realTest finiteTest))
        parameter (rationalGroup flag.out⁻¹ * point) binary‖ ∂BinaryHaar.measure) ≤
      ∫ binary in BinaryFundamentalDomain.domain,
        ‖VectorAbsoluteTheta.function data family (BanachAdelicTheta.tensorTest realTest finiteTest) parameter point binary‖ ∂BinaryHaar.measure := by
  rw [(hasSum data family continuous realTest finiteTest finiteContinuous finiteSupport parameter point halfPlane).tsum_eq]
  apply integral_mono
    (VectorMatrixSeries.sum_norm_integrable data family continuous realTest finiteTest finiteContinuous finiteSupport
      parameter point halfPlane (Subtype.val : Frame → Rectangular ℚ) Subtype.val_injective GodementQuotientIntegrability.frame_nonzero)
    (VectorAbsoluteThetaDecay.integrable_domain data family continuous realTest finiteTest finiteContinuous finiteSupport parameter point halfPlane).norm
  intro binary
  exact VectorMatrixSeries.sum_norm_bound data family continuous realTest finiteTest finiteContinuous finiteSupport
    parameter point binary (Subtype.val : Frame → Rectangular ℚ) Subtype.val_injective GodementQuotientIntegrability.frame_nonzero

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.VectorRawNormSeries
