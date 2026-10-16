module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Cuspidal.TensorCalculus
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Analytic.PartialDerivative
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.AdditiveTwoCocyclePrimitive

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {V : Type} [AddCommGroup V] [Module ℂ V] {index : Type} [Fintype index]

theorem cuspidalTwoCocycleTangent_exists (cusp : CuspidalRepresentation) (basis : Module.Basis index ℂ V)
    (cycle : ℝ → ℝ → cuspidalTensorValues cusp V)
    (regular : ContDiff ℝ 1 (fun point : ℝ × ℝ =>
      cuspidalTensorHilbertEmbedding cusp basis (cycle point.1 point.2)))
    (fixed : ∀ first second, cycle first second ∈ cuspidalTensorFiniteLevel cusp V)
    (analytic : ∀ first : ℝ, AnalyticAt ℝ
      (fun point : (BinaryRealMatrix × ℝ) × ℝ =>
        binaryHilbertTranslation cusp (atInfinity (invertibleMatrix point.1.1))
          (cuspidalTensorHilbertEmbedding cusp basis (cycle point.1.2 point.2))) ((1, first), 0)) :
    ∃ tangent : ℝ → cuspidalTensorValues cusp V,
      (∀ first, cuspidalTensorHilbertEmbedding cusp basis (tangent first) =
        additiveTwoCocycleTangent (fun first second =>
          cuspidalTensorHilbertEmbedding cusp basis (cycle first second)) first) ∧
      (∀ first, tangent first ∈ cuspidalTensorFiniteLevel cusp V) ∧
      (∀ first : ℝ, AnalyticAt ℝ
        (fun point : BinaryRealMatrix × ℝ =>
          binaryHilbertTranslation cusp (atInfinity (invertibleMatrix point.1))
            (cuspidalTensorHilbertEmbedding cusp basis (tangent point.2))) (1, first)) := by
  let hilbertCycle (first second : ℝ) := cuspidalTensorHilbertEmbedding cusp basis (cycle first second)
  have derivative (first : ℝ) := additiveTwoCocycleTangent_derivative hilbertCycle regular first
  have existence (first : ℝ) : ∃ vector : cuspidalTensorValues cusp V,
      cuspidalTensorHilbertEmbedding cusp basis vector = additiveTwoCocycleTangent hilbertCycle first ∧
      vector ∈ cuspidalTensorFiniteLevel cusp V := by
    have slice : AnalyticAt ℝ
        (fun point : BinaryRealMatrix × ℝ => binaryHilbertTranslation cusp (atInfinity (invertibleMatrix point.1))
          (hilbertCycle first point.2)) (1, 0) := by
      exact (analytic first).comp (f := fun point : BinaryRealMatrix × ℝ => ((point.1, first), point.2))
        (x := (1, 0))
        ((analyticAt_fst.prod analyticAt_const).prod analyticAt_snd)
    obtain ⟨vector, equality, level⟩ := cuspidalTensorDeriv_exists cusp basis (cycle first) 0
      (derivative first).differentiableAt (fixed first) slice
    exact ⟨vector, equality.trans (derivative first).deriv, level⟩
  choose tangent tangent_eq tangent_fixed using existence
  refine ⟨tangent, tangent_eq, tangent_fixed, ?_⟩
  intro first
  have partial_analytic := analyticAt_partialDeriv
    (fun point : (BinaryRealMatrix × ℝ) × ℝ =>
      binaryHilbertTranslation cusp (atInfinity (invertibleMatrix point.1.1))
        (hilbertCycle point.1.2 point.2)) (1, first) 0 (analytic first)
  convert partial_analytic using 1
  funext point
  rw [tangent_eq]
  exact (((binaryHilbertTranslation cusp (atInfinity (invertibleMatrix point.1))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
    0 (derivative point.2)).deriv.symm

end TernaryPeriodPolynomials.SphericalDetection.Helpers
