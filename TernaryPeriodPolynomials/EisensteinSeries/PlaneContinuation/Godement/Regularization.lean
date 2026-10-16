module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Godement.ScalingFactor

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.GodementIntegral TernaryPeriodPolynomials.PlaneEisensteinContinuation.GodementUnfolding TernaryPeriodPolynomials.PlaneEisensteinContinuation.GodementRealScaling
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.GodementAbsolute
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.SchwartzRegularization

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.GodementRegularization

theorem raw_integrable_at {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (fixed : vector.val ∈ fixedSubspace data.cusp finiteCongruence)
    (realTest : SchwartzMap RealSpace ℂ) (finiteTest : Rectangular FiniteAdeles → ℂ)
    (finiteContinuous : Continuous finiteTest) (finiteSupport : HasCompactSupport finiteTest)
    (parameter : ℂ) (point : AdelicGL) (halfPlane : (1 - (degree : ℝ)) / 2 < parameter.re) :
    Integrable (rawKernel data (AdelicSchwartzTheta.tensorTest realTest finiteTest) vector parameter point) BinaryHaar.measure := by
  let flag : Flags .plane := QuotientGroup.mk 1
  have result := RawGodementIntegrability.raw_integrable data vector fixed realTest finiteTest finiteContinuous finiteSupport
    parameter (rationalGroup flag.out * point) ((RawGodementIntegrability.halfPlane_iff degree parameter).mpr halfPlane) flag
  simpa only [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul] using result

theorem section_sub_smul {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (fixed : vector.val ∈ fixedSubspace data.cusp finiteCongruence)
    (first second : SchwartzMap RealSpace ℂ) (coefficient : ℂ) (finiteTest : Rectangular FiniteAdeles → ℂ)
    (finiteContinuous : Continuous finiteTest) (finiteSupport : HasCompactSupport finiteTest)
    (parameter : ℂ) (point : AdelicGL) (halfPlane : (1 - (degree : ℝ)) / 2 < parameter.re) :
    sectionFunction data (AdelicSchwartzTheta.tensorTest (first - coefficient • second) finiteTest) vector parameter point =
      sectionFunction data (AdelicSchwartzTheta.tensorTest first finiteTest) vector parameter point -
        coefficient * sectionFunction data (AdelicSchwartzTheta.tensorTest second finiteTest) vector parameter point := by
  have equation : rawKernel data (AdelicSchwartzTheta.tensorTest (first - coefficient • second) finiteTest) vector parameter point =
      fun binary => rawKernel data (AdelicSchwartzTheta.tensorTest first finiteTest) vector parameter point binary -
        coefficient * rawKernel data (AdelicSchwartzTheta.tensorTest second finiteTest) vector parameter point binary := by
    funext binary
    simp only [rawKernel, RectangularKernel.kernel, AdelicSchwartzTheta.tensorTest, _root_.sub_apply, _root_.smul_apply, smul_eq_mul]
    ring
  change GodementIntegral.outerCharacter data parameter (GeneralLinearGroup.det point) *
    (∫ binary, rawKernel data (AdelicSchwartzTheta.tensorTest (first - coefficient • second) finiteTest) vector parameter point binary ∂BinaryHaar.measure) = _
  rw [equation, integral_sub (raw_integrable_at data vector fixed first finiteTest finiteContinuous finiteSupport parameter point halfPlane)
    ((raw_integrable_at data vector fixed second finiteTest finiteContinuous finiteSupport parameter point halfPlane).const_mul coefficient), integral_const_mul]
  change _ = GodementIntegral.outerCharacter data parameter (GeneralLinearGroup.det point) *
      (∫ binary, rawKernel data (AdelicSchwartzTheta.tensorTest first finiteTest) vector parameter point binary ∂BinaryHaar.measure) -
    coefficient * (GodementIntegral.outerCharacter data parameter (GeneralLinearGroup.det point) *
      (∫ binary, rawKernel data (AdelicSchwartzTheta.tensorTest second finiteTest) vector parameter point binary ∂BinaryHaar.measure))
  ring

theorem section_difference {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (fixed : vector.val ∈ fixedSubspace data.cusp finiteCongruence)
    (realTest : SchwartzMap RealSpace ℂ) (coefficient : ℂ) (finiteTest : Rectangular FiniteAdeles → ℂ)
    (finiteContinuous : Continuous finiteTest) (finiteSupport : HasCompactSupport finiteTest)
    (parameter : ℂ) (point : AdelicGL) (halfPlane : (1 - (degree : ℝ)) / 2 < parameter.re) :
    sectionFunction data (AdelicSchwartzTheta.tensorTest (realTest - coefficient • RealFourierScaling.dilate realTest scale) finiteTest) vector parameter point =
      (1 - coefficient * multiplier data scale parameter) * sectionFunction data (AdelicSchwartzTheta.tensorTest realTest finiteTest) vector parameter point := by
  rw [section_sub_smul data vector fixed realTest _ coefficient finiteTest finiteContinuous finiteSupport parameter point halfPlane,
    section_dilate data vector realTest finiteTest scale scale_pos]
  ring

theorem section_regularize {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (fixed : vector.val ∈ fixedSubspace data.cusp finiteCongruence)
    (realTest : SchwartzMap RealSpace ℂ) (finiteTest : Rectangular FiniteAdeles → ℂ)
    (finiteContinuous : Continuous finiteTest) (finiteSupport : HasCompactSupport finiteTest)
    (parameter : ℂ) (point : AdelicGL) (halfPlane : (1 - (degree : ℝ)) / 2 < parameter.re) :
    sectionFunction data (AdelicSchwartzTheta.tensorTest (regularize realTest) finiteTest) vector parameter point =
      GodementScalingFactor.regularizationFactor data parameter *
        sectionFunction data (AdelicSchwartzTheta.tensorTest realTest finiteTest) vector parameter point := by
  unfold regularize killFourier
  rw [section_difference data vector fixed (killValue realTest) 64 finiteTest finiteContinuous finiteSupport parameter point halfPlane]
  have first := section_difference data vector fixed realTest 1 finiteTest finiteContinuous finiteSupport parameter point halfPlane
  simp only [one_smul, one_mul] at first
  rw [killValue, first]
  unfold GodementScalingFactor.regularizationFactor
  ring

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.GodementRegularization
