module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Banach.ThetaFamilies
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Vector.ThetaIntegral

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.SobolevSeminorms TernaryPeriodPolynomials.PlaneEisensteinContinuation.BanachCuspDecay

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.VectorThetaFamilies

variable {Source : Type} [NormedAddCommGroup Source] [NormedSpace ℂ Source] [CompleteSpace Source]

theorem theta_differentiable {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (continuous : Continuous (fun vector => (family vector).val.val))
    (tests : ℂ → SchwartzMap RealSpace Source)
    (holomorphic : ∀ vector, Differentiable ℂ (fun parameter => tests parameter vector))
    (bounded : ∀ compact : Set ℂ, IsCompact compact → UniformSchwartzBounds.Bounded (tests '' compact))
    (finiteTest : Rectangular FiniteAdeles → ℂ) (finiteContinuous : Continuous finiteTest)
    (finiteSupport : HasCompactSupport finiteTest) (point : AdelicGL) (binary : BinaryAdelicGL) :
    Differentiable ℂ (fun parameter => VectorTheta.fullTheta data family
      (BanachAdelicTheta.tensorTest (tests parameter) finiteTest) point binary) :=
  (evaluation data family continuous binary).differentiable.comp
    (BanachThetaFamilies.differentiable tests holomorphic bounded finiteTest finiteContinuous finiteSupport point binary)

theorem integrand_differentiable {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (continuous : Continuous (fun vector => (family vector).val.val))
    (tests : ℂ → SchwartzMap RealSpace Source)
    (holomorphic : ∀ vector, Differentiable ℂ (fun parameter => tests parameter vector))
    (bounded : ∀ compact : Set ℂ, IsCompact compact → UniformSchwartzBounds.Bounded (tests '' compact))
    (finiteTest : Rectangular FiniteAdeles → ℂ) (finiteContinuous : Continuous finiteTest)
    (finiteSupport : HasCompactSupport finiteTest) (point : AdelicGL) (binary : BinaryAdelicGL) :
    Differentiable ℂ (fun parameter => VectorThetaIntegral.integrand data family
      (BanachAdelicTheta.tensorTest (tests parameter) finiteTest) point parameter binary) := by
  have character : Differentiable ℂ (fun parameter =>
      GodementIntegral.innerCharacter data parameter (GeneralLinearGroup.det binary)) := by
    have equality : (fun parameter => GodementIntegral.innerCharacter data parameter (GeneralLinearGroup.det binary)) =
        fun parameter => GodementIntegral.innerCharacter data 0 (GeneralLinearGroup.det binary) *
          Complex.exp (parameter * (Real.log (adeleNorm (GeneralLinearGroup.det binary) : ℝ) : ℂ)) := by
      funext parameter
      exact LargeThetaIntegral.character_factor data parameter _
    rw [equality]
    fun_prop
  apply Differentiable.mul
  · exact character
  · exact theta_differentiable data family continuous tests holomorphic bounded finiteTest finiteContinuous finiteSupport point binary

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.VectorThetaFamilies
