module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Vector.Regularization

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.ZeroConstantThetaDecay
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.BanachSchwartzRegularization TernaryPeriodPolynomials.PlaneEisensteinContinuation.GodementScalingFactor
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.SobolevSeminorms TernaryPeriodPolynomials.PlaneEisensteinContinuation.VectorMatrixOrbit

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.VectorGodementContinuation

variable {Source : Type*} [NormedAddCommGroup Source] [NormedSpace ℂ Source] [CompleteSpace Source]

def continuation {degree : ℕ} (data : InducingData degree) (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (realTest : SchwartzMap RealSpace Source) (finiteScale : FiniteAdelesˣ) (offset : FiniteRectangularFourier.Space)
    (parameter : ℂ) (point : AdelicGL) : ℂ :=
  VectorThetaIntegral.continuation data family
    (BanachAdelicTheta.tensorTest (regularize realTest) (RectangularAdelicPoisson.finiteTest finiteScale offset)) parameter point /
      regularizationFactor data parameter

theorem meromorphic {degree : ℕ} (data : InducingData degree) (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (continuous : Continuous (fun vector => (family vector).val.val))
    (realTest : SchwartzMap RealSpace Source) (finiteScale : FiniteAdelesˣ) (offset : FiniteRectangularFourier.Space)
    (point : AdelicGL) (parameter : ℂ) : MeromorphicAt (fun parameter => continuation data family realTest finiteScale offset parameter point) parameter :=
  ((VectorThetaIntegral.continuation_differentiable data family continuous (regularize realTest)
    (regularize_zero realTest) (regularize_fourier_zero realTest) finiteScale offset point).analyticAt parameter).meromorphicAt.div
      ((factor_differentiable data).analyticAt parameter).meromorphicAt

theorem eisenstein_hasSum {degree : ℕ} (data : InducingData degree) (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (continuous : Continuous (fun vector => (family vector).val.val))
    (realTest : SchwartzMap RealSpace Source) (finiteScale : FiniteAdelesˣ) (offset : FiniteRectangularFourier.Space)
    (point : AdelicGL) (parameter : ℂ) (halfPlane : (1 - (degree : ℝ)) / 2 < parameter.re) :
    HasSum (fun flag => eisensteinSummand (VectorGodement.sectionFunction data
      (liftTest data family (BanachAdelicTheta.tensorTest realTest (RectangularAdelicPoisson.finiteTest finiteScale offset)))) parameter point flag)
      (continuation data family realTest finiteScale offset parameter point) := by
  have result := (VectorUnfolding.eisenstein_hasSum data family continuous (regularize realTest) (regularize_zero realTest) _
    (finiteTest_continuous finiteScale offset) (finiteTest_compactSupport finiteScale offset) parameter point halfPlane).mul_left
    (regularizationFactor data parameter)⁻¹
  have factorNonzero := factor_nonzero data parameter halfPlane
  have valueEquality : (regularizationFactor data parameter)⁻¹ *
      VectorThetaIntegral.continuation data family
        (BanachAdelicTheta.tensorTest (regularize realTest) (RectangularAdelicPoisson.finiteTest finiteScale offset)) parameter point =
      continuation data family realTest finiteScale offset parameter point := by
    unfold continuation
    rw [div_eq_mul_inv, mul_comm]
  rw [valueEquality] at result
  apply result.congr_fun
  intro flag
  unfold eisensteinSummand
  rw [VectorRegularization.section_regularize data family continuous realTest _
    (finiteTest_continuous finiteScale offset) (finiteTest_compactSupport finiteScale offset) parameter _ halfPlane,
    inv_mul_cancel_left₀ factorNonzero]

theorem isEisensteinContinuation {degree : ℕ} (data : InducingData degree) (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (continuous : Continuous (fun vector => (family vector).val.val))
    (realTest : SchwartzMap RealSpace Source) (finiteScale : FiniteAdelesˣ) (offset : FiniteRectangularFourier.Space) :
    IsEisensteinContinuation
      (VectorGodement.sectionFunction data (liftTest data family (BanachAdelicTheta.tensorTest realTest (RectangularAdelicPoisson.finiteTest finiteScale offset))))
      (continuation data family realTest finiteScale offset) :=
  ⟨fun point parameter => meromorphic data family continuous realTest finiteScale offset point parameter,
    (1 - (degree : ℝ)) / 2, fun parameter halfPlane point => eisenstein_hasSum data family continuous realTest finiteScale offset point parameter halfPlane⟩

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.VectorGodementContinuation
