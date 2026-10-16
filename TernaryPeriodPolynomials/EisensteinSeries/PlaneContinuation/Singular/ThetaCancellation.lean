module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Singular.OrbitCancellation
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Singular.MatrixSeries

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularTheta
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.MatrixStabilizerDomain TernaryPeriodPolynomials.PlaneEisensteinContinuation.SingularOrbitPartition TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.SingularThetaCancellation

theorem fiber_integral_sum_zero {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (fixed : vector.val ∈ fixedSubspace data.cusp finiteCongruence)
    (realTest : SchwartzMap RealSpace ℂ) (finiteTest : Rectangular FiniteAdeles → ℂ)
    (finiteContinuous : Continuous finiteTest) (finiteSupport : HasCompactSupport finiteTest)
    (parameter : ℂ) (point : AdelicGL) (halfPlane : 7 < 2 * WeightedAbsoluteTheta.exponent degree parameter) (orbit : Orbit) :
    (∑' matrix : {matrix : RankOne // orbitClass matrix = orbit}, ∫ binary in BinaryFundamentalDomain.domain,
      term data (AdelicSchwartzTheta.tensorTest realTest finiteTest) vector parameter point matrix.val.val binary ∂BinaryHaar.measure) = 0 := by
  rw [← (fiberEquiv orbit).tsum_eq]
  simp only [fiberEquiv_val]
  rw [(MatrixOrbitIntegrability.hasSum_integral data vector fixed realTest finiteTest finiteContinuous finiteSupport parameter point halfPlane
    orbit.out.val orbit.out.property.1).tsum_eq]
  exact SingularOrbitCancellation.integral_zero data vector fixed realTest finiteTest finiteContinuous finiteSupport parameter point halfPlane
    orbit.out.val orbit.out.property.1 orbit.out.property.2

theorem singular_integral_zero {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (fixed : vector.val ∈ fixedSubspace data.cusp finiteCongruence)
    (realTest : SchwartzMap RealSpace ℂ) (finiteTest : Rectangular FiniteAdeles → ℂ)
    (finiteContinuous : Continuous finiteTest) (finiteSupport : HasCompactSupport finiteTest)
    (parameter : ℂ) (point : AdelicGL) (halfPlane : 7 < 2 * WeightedAbsoluteTheta.exponent degree parameter) :
    (∫ binary in BinaryFundamentalDomain.domain,
      (singularTheta (AdelicSchwartzTheta.tensorTest realTest finiteTest) point binary - AdelicSchwartzTheta.tensorTest realTest finiteTest 0) *
        GodementIntegral.innerCharacter data parameter (GeneralLinearGroup.det binary) * data.cusp.realize vector binary ∂BinaryHaar.measure) = 0 := by
  have fiberSum := (SingularMatrixSeries.hasSum_integral data vector fixed realTest finiteTest finiteContinuous finiteSupport parameter point halfPlane).tsum_fiberwise orbitClass
  have vanishing : ∀ orbit : Orbit,
      (∑' matrix : ↑(orbitClass ⁻¹' {orbit}), ∫ binary in BinaryFundamentalDomain.domain,
        term data (AdelicSchwartzTheta.tensorTest realTest finiteTest) vector parameter point matrix.val.val binary ∂BinaryHaar.measure) = 0 :=
    fiber_integral_sum_zero data vector fixed realTest finiteTest finiteContinuous finiteSupport parameter point halfPlane
  simpa only [vanishing, tsum_zero] using fiberSum.tsum_eq.symm

theorem nonzero_integral_eq_frame {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (fixed : vector.val ∈ fixedSubspace data.cusp finiteCongruence)
    (realTest : SchwartzMap RealSpace ℂ) (finiteTest : Rectangular FiniteAdeles → ℂ)
    (finiteContinuous : Continuous finiteTest) (finiteSupport : HasCompactSupport finiteTest)
    (parameter : ℂ) (point : AdelicGL) (halfPlane : 7 < 2 * WeightedAbsoluteTheta.exponent degree parameter) :
    (∫ binary in BinaryFundamentalDomain.domain,
      (fullTheta (AdelicSchwartzTheta.tensorTest realTest finiteTest) point binary - AdelicSchwartzTheta.tensorTest realTest finiteTest 0) *
        GodementIntegral.innerCharacter data parameter (GeneralLinearGroup.det binary) * data.cusp.realize vector binary ∂BinaryHaar.measure) =
      ∫ binary in BinaryFundamentalDomain.domain,
        ThetaInvariance.integrand data (AdelicSchwartzTheta.tensorTest realTest finiteTest) vector parameter point binary ∂BinaryHaar.measure := by
  have difference : (fun binary =>
      (fullTheta (AdelicSchwartzTheta.tensorTest realTest finiteTest) point binary - AdelicSchwartzTheta.tensorTest realTest finiteTest 0) *
        GodementIntegral.innerCharacter data parameter (GeneralLinearGroup.det binary) * data.cusp.realize vector binary) -
      ThetaInvariance.integrand data (AdelicSchwartzTheta.tensorTest realTest finiteTest) vector parameter point =
      fun binary => (singularTheta (AdelicSchwartzTheta.tensorTest realTest finiteTest) point binary - AdelicSchwartzTheta.tensorTest realTest finiteTest 0) *
        GodementIntegral.innerCharacter data parameter (GeneralLinearGroup.det binary) * data.cusp.realize vector binary := by
    funext binary
    simp only [Pi.sub_apply, ThetaInvariance.integrand]
    rw [AdelicSchwartzTheta.decomposition realTest finiteTest finiteContinuous finiteSupport point binary]
    ring
  have vanishing := singular_integral_zero data vector fixed realTest finiteTest finiteContinuous finiteSupport parameter point halfPlane
  rw [← difference, integral_sub'
    (NonzeroThetaIntegrability.nonzero_integrable data vector fixed realTest finiteTest finiteContinuous finiteSupport parameter point halfPlane)
    (NonzeroThetaIntegrability.frame_integrable data vector fixed realTest finiteTest finiteContinuous finiteSupport parameter point halfPlane)] at vanishing
  exact sub_eq_zero.mp vanishing

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.SingularThetaCancellation
