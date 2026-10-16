module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Uniform.ThetaMajorants
public import Mathlib.Analysis.Complex.LocallyUniformLimit

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz TernaryPeriodPolynomials.PlaneEisensteinContinuation.ThetaParameterBounds
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.BanachAdelicTheta

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.BanachThetaFamilies

variable {Target : Type} [NormedAddCommGroup Target] [NormedSpace ℂ Target] [CompleteSpace Target]

omit [CompleteSpace Target] in
theorem term_differentiable (tests : ℂ → SchwartzMap RealSpace Target)
    (holomorphic : ∀ vector, Differentiable ℂ (fun parameter => tests parameter vector))
    (finiteTest : Rectangular FiniteAdeles → ℂ) (point : AdelicGL) (binary : BinaryAdelicGL)
    (matrix : Rectangular ℚ) :
    Differentiable ℂ (fun parameter => matrixTerm (tensorTest (tests parameter) finiteTest) point binary matrix) := by
  simp only [matrixTerm_factorization (parameter := (point, binary))]
  exact (holomorphic _).const_smul _

theorem differentiable (tests : ℂ → SchwartzMap RealSpace Target)
    (holomorphic : ∀ vector, Differentiable ℂ (fun parameter => tests parameter vector))
    (bounded : ∀ compact : Set ℂ, IsCompact compact → UniformSchwartzBounds.Bounded (tests '' compact))
    (finiteTest : Rectangular FiniteAdeles → ℂ) (finiteContinuous : Continuous finiteTest)
    (finiteSupport : HasCompactSupport finiteTest) (point : AdelicGL) (binary : BinaryAdelicGL) :
    Differentiable ℂ (fun parameter => fullTheta (tensorTest (tests parameter) finiteTest) point binary) := by
  intro center
  obtain ⟨majorant, summableMajorant, _, majorantBound⟩ := UniformThetaMajorants.adelic
    (tests '' Metric.closedBall center 1) (bounded _ (isCompact_closedBall center 1))
    finiteTest finiteContinuous finiteSupport {(point, binary)} isCompact_singleton
  apply (Complex.differentiableOn_tsum_of_summable_norm summableMajorant
    (fun matrix => (term_differentiable tests holomorphic finiteTest point binary matrix).differentiableOn)
    Metric.isOpen_ball (fun matrix parameter membership =>
      majorantBound (tests parameter) ⟨parameter, Metric.ball_subset_closedBall membership, rfl⟩
        (point, binary) (Set.mem_singleton _) matrix)).differentiableAt
  exact Metric.ball_mem_nhds _ zero_lt_one

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.BanachThetaFamilies
