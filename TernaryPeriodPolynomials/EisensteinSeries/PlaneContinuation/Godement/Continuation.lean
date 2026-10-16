module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Godement.Regularization

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.ZeroConstantThetaDecay
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.SchwartzRegularization TernaryPeriodPolynomials.PlaneEisensteinContinuation.GodementScalingFactor

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.GodementContinuation

def continuation {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (realTest : SchwartzMap RealSpace ℂ) (finiteScale : FiniteAdelesˣ) (offset : FiniteRectangularFourier.Space)
    (parameter : ℂ) (point : AdelicGL) : ℂ :=
  ZeroConstantThetaIntegral.continuation data
    (AdelicSchwartzTheta.tensorTest (regularize realTest) (RectangularAdelicPoisson.finiteTest finiteScale offset)) vector parameter point /
      regularizationFactor data parameter

theorem meromorphic {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (fixed : vector.val ∈ fixedSubspace data.cusp finiteCongruence)
    (realTest : SchwartzMap RealSpace ℂ) (finiteScale : FiniteAdelesˣ) (offset : FiniteRectangularFourier.Space)
    (point : AdelicGL) (parameter : ℂ) : MeromorphicAt (fun parameter => continuation data vector realTest finiteScale offset parameter point) parameter :=
  ((ZeroConstantThetaIntegral.continuation_differentiable data vector fixed (regularize realTest)
    (regularize_zero realTest) (regularize_fourier_zero realTest) finiteScale offset point).analyticAt parameter).meromorphicAt.div
      ((factor_differentiable data).analyticAt parameter).meromorphicAt

theorem eisenstein_hasSum {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (fixed : vector.val ∈ fixedSubspace data.cusp finiteCongruence)
    (realTest : SchwartzMap RealSpace ℂ) (finiteScale : FiniteAdelesˣ) (offset : FiniteRectangularFourier.Space)
    (point : AdelicGL) (parameter : ℂ) (halfPlane : (1 - (degree : ℝ)) / 2 < parameter.re) :
    HasSum (fun flag => eisensteinSummand (GodementIntegral.sectionFunction data
      (AdelicSchwartzTheta.tensorTest realTest (RectangularAdelicPoisson.finiteTest finiteScale offset)) vector) parameter point flag)
      (continuation data vector realTest finiteScale offset parameter point) := by
  have result := (ZeroConstantThetaIntegral.eisenstein_hasSum data vector fixed (regularize realTest) finiteScale offset point parameter halfPlane).mul_left
    (regularizationFactor data parameter)⁻¹
  have factorNonzero := factor_nonzero data parameter halfPlane
  have valueEquality : (regularizationFactor data parameter)⁻¹ *
      ZeroConstantThetaIntegral.continuation data
        (AdelicSchwartzTheta.tensorTest (regularize realTest) (RectangularAdelicPoisson.finiteTest finiteScale offset)) vector parameter point =
      continuation data vector realTest finiteScale offset parameter point := by
    unfold continuation
    rw [div_eq_mul_inv, mul_comm]
  rw [valueEquality] at result
  apply result.congr_fun
  intro flag
  unfold eisensteinSummand
  rw [GodementRegularization.section_regularize data vector fixed realTest _
    (finiteTest_continuous finiteScale offset) (finiteTest_compactSupport finiteScale offset) parameter _ halfPlane,
    inv_mul_cancel_left₀ factorNonzero]

theorem isEisensteinContinuation {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (fixed : vector.val ∈ fixedSubspace data.cusp finiteCongruence)
    (realTest : SchwartzMap RealSpace ℂ) (finiteScale : FiniteAdelesˣ) (offset : FiniteRectangularFourier.Space) :
    IsEisensteinContinuation
      (GodementIntegral.sectionFunction data (AdelicSchwartzTheta.tensorTest realTest (RectangularAdelicPoisson.finiteTest finiteScale offset)) vector)
      (continuation data vector realTest finiteScale offset) :=
  ⟨fun point parameter => meromorphic data vector fixed realTest finiteScale offset point parameter,
    (1 - (degree : ℝ)) / 2, fun parameter halfPlane point => eisenstein_hasSum data vector fixed realTest finiteScale offset point parameter halfPlane⟩

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.GodementContinuation
