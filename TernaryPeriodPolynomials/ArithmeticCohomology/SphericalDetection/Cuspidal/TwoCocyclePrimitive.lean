module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Cuspidal.TwoCocycleTangent
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Cuspidal.TensorPrimitive

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {V : Type} [AddCommGroup V] [Module ℂ V] {index : Type} [Fintype index]

theorem cuspidalTwoCocycle_exists_primitive (cusp : CuspidalRepresentation) (basis : Module.Basis index ℂ V)
    (action : ℝ → Module.End ℂ (cuspidalTensorValues cusp V))
    (hilbertAction : ℝ → (index → cusp.H) →L[ℝ] (index → cusp.H))
    (intertwines : ∀ parameter vector, cuspidalTensorHilbertEmbedding cusp basis (action parameter vector) =
      hilbertAction parameter (cuspidalTensorHilbertEmbedding cusp basis vector))
    (cycle : ℝ → ℝ → cuspidalTensorValues cusp V)
    (cocycle : ∀ first second third,
      cycle (first + second) third + cycle first second = action first (cycle second third) + cycle first (second + third))
    (origin : ∀ first, cycle first 0 = 0)
    (regular : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun point : ℝ × ℝ =>
      cuspidalTensorHilbertEmbedding cusp basis (cycle point.1 point.2)))
    (fixed : ∀ first second, cycle first second ∈ cuspidalTensorFiniteLevel cusp V)
    (analytic : ∀ first : ℝ, AnalyticAt ℝ
      (fun point : (BinaryRealMatrix × ℝ) × ℝ =>
        binaryHilbertTranslation cusp (atInfinity (invertibleMatrix point.1.1))
          (cuspidalTensorHilbertEmbedding cusp basis (cycle point.1.2 point.2))) ((1, first), 0)) :
    ∃ primitive : ℝ → cuspidalTensorValues cusp V,
      primitive 0 = 0 ∧ (∀ parameter, primitive parameter ∈ cuspidalTensorFiniteLevel cusp V) ∧
      ContDiff ℝ (↑(⊤ : ℕ∞)) (fun parameter => cuspidalTensorHilbertEmbedding cusp basis (primitive parameter)) ∧
      (∀ center : ℝ, AnalyticAt ℝ
        (fun point : BinaryRealMatrix × ℝ => binaryHilbertTranslation cusp (atInfinity (invertibleMatrix point.1))
          (cuspidalTensorHilbertEmbedding cusp basis (primitive point.2))) (1, center)) ∧
      ∀ first second, cycle first second = action first (primitive second) - primitive (first + second) + primitive first := by
  let hilbertCycle (first second : ℝ) := cuspidalTensorHilbertEmbedding cusp basis (cycle first second)
  have differentiable : ContDiff ℝ 1 (Function.uncurry hilbertCycle) := regular.of_le (by simp)
  obtain ⟨tangent, tangent_eq, tangent_fixed, tangent_analytic⟩ :=
    cuspidalTwoCocycleTangent_exists cusp basis cycle differentiable fixed analytic
  have tangent_regular : ContDiff ℝ (↑(⊤ : ℕ∞))
      (fun parameter => cuspidalTensorHilbertEmbedding cusp basis (tangent parameter)) := by
    have smoothCycle : ContDiff ℝ ((↑(⊤ : ℕ∞) : WithTop ℕ∞) + 1) (Function.uncurry hilbertCycle) := by
      convert regular using 1
      · simp
      · rfl
    have smoothTangent := additiveTwoCocycleTangent_contDiff hilbertCycle smoothCycle
    convert smoothTangent using 1
    funext parameter
    exact tangent_eq parameter
  obtain ⟨primitive, primitive_eq, primitive_zero, primitive_fixed, primitive_regular, primitive_analytic⟩ :=
    cuspidalTensorPrimitive_exists cusp basis tangent tangent_regular tangent_fixed tangent_analytic
  refine ⟨primitive, primitive_zero, primitive_fixed, primitive_regular, primitive_analytic, ?_⟩
  intro first second
  apply cuspidalTensorHilbertEmbedding_injective cusp basis
  rw [map_add, map_sub, intertwines, primitive_eq, primitive_eq, primitive_eq]
  have relation (left middle right : ℝ) :
      hilbertCycle (left + middle) right + hilbertCycle left middle =
        hilbertAction left (hilbertCycle middle right) + hilbertCycle left (middle + right) := by
    have mapped := congrArg (cuspidalTensorHilbertEmbedding cusp basis) (cocycle left middle right)
    simpa only [map_add, intertwines] using mapped
  have hilbert_origin (left : ℝ) : hilbertCycle left 0 = 0 := by simp [hilbertCycle, origin]
  have derivative (left : ℝ) : HasDerivAt (hilbertCycle left)
      (cuspidalTensorHilbertEmbedding cusp basis (tangent left)) 0 := by
    rw [tangent_eq]
    exact additiveTwoCocycleTangent_derivative hilbertCycle differentiable left
  exact additiveTwoCocyclePrimitive_boundary hilbertAction hilbertCycle relation hilbert_origin
    (fun parameter => cuspidalTensorHilbertEmbedding cusp basis (tangent parameter)) derivative
      tangent_regular.continuous first second

end TernaryPeriodPolynomials.SphericalDetection.Helpers
