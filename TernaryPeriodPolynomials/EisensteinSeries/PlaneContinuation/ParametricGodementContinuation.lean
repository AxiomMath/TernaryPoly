module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Uniform.VectorIntegral
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.RegularizedTestFamilies
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Vector.GodementContinuation

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.ZeroConstantThetaDecay
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.BanachSchwartzRegularization TernaryPeriodPolynomials.PlaneEisensteinContinuation.GodementScalingFactor
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.SobolevSeminorms TernaryPeriodPolynomials.PlaneEisensteinContinuation.VectorMatrixOrbit

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.ParametricGodementContinuation

variable {Source : Type} [NormedAddCommGroup Source] [NormedSpace ℂ Source] [CompleteSpace Source]

theorem meromorphic {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (continuous : Continuous (fun vector => (family vector).val.val))
    (tests : ℂ → SchwartzMap RealSpace Source)
    (holomorphic : ∀ vector, Differentiable ℂ (fun parameter => tests parameter vector))
    (bounded : ∀ compact : Set ℂ, IsCompact compact → UniformSchwartzBounds.Bounded (tests '' compact))
    (finiteScale : FiniteAdelesˣ) (offset : FiniteRectangularFourier.Space) (point : AdelicGL) (parameter : ℂ) :
    MeromorphicAt (fun parameter => VectorGodementContinuation.continuation data family (tests parameter)
      finiteScale offset parameter point) parameter := by
  have integralDifferentiable := UniformVectorIntegral.differentiable data family continuous
    (fun parameter => regularize (tests parameter))
    (RegularizedTestFamilies.pointwise_differentiable tests holomorphic)
    (fun compact compactIs => RegularizedTestFamilies.family_bounded tests compact (bounded compact compactIs))
    (fun parameter => regularize_zero (tests parameter))
    (fun parameter => regularize_fourier_zero (tests parameter)) finiteScale offset point
  have numerator := (ZeroConstantThetaIntegral.outer_differentiable data (Matrix.GeneralLinearGroup.det point)).mul integralDifferentiable
  exact (numerator.analyticAt parameter).meromorphicAt.div
    ((factor_differentiable data).analyticAt parameter).meromorphicAt

theorem isEisensteinContinuation {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (continuous : Continuous (fun vector => (family vector).val.val))
    (tests : ℂ → SchwartzMap RealSpace Source)
    (holomorphic : ∀ vector, Differentiable ℂ (fun parameter => tests parameter vector))
    (bounded : ∀ compact : Set ℂ, IsCompact compact → UniformSchwartzBounds.Bounded (tests '' compact))
    (finiteScale : FiniteAdelesˣ) (offset : FiniteRectangularFourier.Space) :
    IsEisensteinContinuation
      (fun parameter point => VectorGodement.sectionFunction data (liftTest data family
        (BanachAdelicTheta.tensorTest (tests parameter) (RectangularAdelicPoisson.finiteTest finiteScale offset))) parameter point)
      (fun parameter point => VectorGodementContinuation.continuation data family (tests parameter) finiteScale offset parameter point) :=
  ⟨fun point parameter => meromorphic data family continuous tests holomorphic bounded finiteScale offset point parameter,
    (1 - (degree : ℝ)) / 2, fun parameter halfPlane point =>
      VectorGodementContinuation.eisenstein_hasSum data family continuous (tests parameter) finiteScale offset point parameter halfPlane⟩

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.ParametricGodementContinuation
