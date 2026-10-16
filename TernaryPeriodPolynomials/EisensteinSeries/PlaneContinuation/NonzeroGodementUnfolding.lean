module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Singular.ThetaCancellation
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.RawGodementIntegrability

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularTheta
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.GodementIntegral TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.NonzeroGodementUnfolding

theorem eisenstein_hasSum {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (fixed : vector.val ∈ fixedSubspace data.cusp finiteCongruence)
    (realTest : SchwartzMap RealSpace ℂ) (finiteTest : Rectangular FiniteAdeles → ℂ)
    (finiteContinuous : Continuous finiteTest) (finiteSupport : HasCompactSupport finiteTest)
    (parameter : ℂ) (point : AdelicGL) (halfPlane : (1 - (degree : ℝ)) / 2 < parameter.re) :
    HasSum (fun flag => eisensteinSummand (sectionFunction data (AdelicSchwartzTheta.tensorTest realTest finiteTest) vector) parameter point flag)
      (outerCharacter data parameter (GeneralLinearGroup.det point) *
        ∫ binary in BinaryFundamentalDomain.domain,
          (fullTheta (AdelicSchwartzTheta.tensorTest realTest finiteTest) point binary - AdelicSchwartzTheta.tensorTest realTest finiteTest 0) *
            innerCharacter data parameter (GeneralLinearGroup.det binary) * data.cusp.realize vector binary ∂BinaryHaar.measure) := by
  have condition := (RawGodementIntegrability.halfPlane_iff degree parameter).mpr halfPlane
  rw [SingularThetaCancellation.nonzero_integral_eq_frame data vector fixed realTest finiteTest finiteContinuous finiteSupport parameter point condition]
  exact RawGodementIntegrability.eisenstein_hasSum data vector fixed realTest finiteTest finiteContinuous finiteSupport parameter point condition

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.NonzeroGodementUnfolding
