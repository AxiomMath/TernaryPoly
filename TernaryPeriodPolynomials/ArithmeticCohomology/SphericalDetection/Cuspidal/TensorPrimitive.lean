module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Cuspidal.TensorCalculus
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Analytic.IntegralEndpoint
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.AdditiveTwoCocyclePrimitive

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {V : Type} [AddCommGroup V] [Module ℂ V] {index : Type} [Fintype index]

theorem cuspidalTensorPrimitive_exists (cusp : CuspidalRepresentation) (basis : Module.Basis index ℂ V)
    (tangent : ℝ → cuspidalTensorValues cusp V)
    (regular : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun parameter => cuspidalTensorHilbertEmbedding cusp basis (tangent parameter)))
    (fixed : ∀ parameter, tangent parameter ∈ cuspidalTensorFiniteLevel cusp V)
    (analytic : ∀ center : ℝ, AnalyticAt ℝ
      (fun point : BinaryRealMatrix × ℝ => binaryHilbertTranslation cusp (atInfinity (invertibleMatrix point.1))
        (cuspidalTensorHilbertEmbedding cusp basis (tangent point.2))) (1, center)) :
    ∃ primitive : ℝ → cuspidalTensorValues cusp V,
      (∀ parameter, cuspidalTensorHilbertEmbedding cusp basis (primitive parameter) =
        additiveTwoCocyclePrimitive (fun sample => cuspidalTensorHilbertEmbedding cusp basis (tangent sample)) parameter) ∧
      primitive 0 = 0 ∧ (∀ parameter, primitive parameter ∈ cuspidalTensorFiniteLevel cusp V) ∧
      ContDiff ℝ (↑(⊤ : ℕ∞)) (fun parameter => cuspidalTensorHilbertEmbedding cusp basis (primitive parameter)) ∧
      (∀ center : ℝ, AnalyticAt ℝ
        (fun point : BinaryRealMatrix × ℝ => binaryHilbertTranslation cusp (atInfinity (invertibleMatrix point.1))
          (cuspidalTensorHilbertEmbedding cusp basis (primitive point.2))) (1, center)) := by
  have existence (parameter : ℝ) := cuspidalTensorIntervalIntegral_exists cusp basis tangent
    regular.continuous fixed analytic 0 parameter
  choose integral integral_eq integral_fixed using existence
  let primitive (parameter : ℝ) := -integral parameter
  let hilbertTangent (parameter : ℝ) := cuspidalTensorHilbertEmbedding cusp basis (tangent parameter)
  have equality (parameter : ℝ) : cuspidalTensorHilbertEmbedding cusp basis (primitive parameter) =
      additiveTwoCocyclePrimitive hilbertTangent parameter := by
    rw [show primitive parameter = -integral parameter from rfl, map_neg, integral_eq]
    rfl
  refine ⟨primitive, equality, ?_, ?_, ?_, ?_⟩
  · apply cuspidalTensorHilbertEmbedding_injective cusp basis
    rw [equality, additiveTwoCocyclePrimitive_zero, map_zero]
  · intro parameter
    exact (cuspidalTensorFiniteLevel cusp V).neg_mem (integral_fixed parameter)
  · have smooth := additiveTwoCocyclePrimitive_contDiff hilbertTangent regular
    simpa [equality] using smooth
  · intro center
    let orbital (point : BinaryRealMatrix × ℝ) :=
      binaryHilbertTranslation cusp (atInfinity (invertibleMatrix point.1)) (hilbertTangent point.2)
    have orbital_continuous (matrix : BinaryRealMatrix) : Continuous (fun sample => orbital (matrix, sample)) :=
      (binaryHilbertTranslation cusp (atInfinity (invertibleMatrix matrix))).continuous.comp regular.continuous
    have integrated := (analyticAt_intervalIntegral_endpoint orbital 1 center orbital_continuous analytic).neg
    convert integrated using 1
    funext point
    rw [equality]
    change binaryHilbertTranslation cusp (atInfinity (invertibleMatrix point.1))
      (-(∫ sample in 0..point.2, hilbertTangent sample)) = -(∫ sample in 0..point.2, orbital (point.1, sample))
    rw [map_neg]
    congr 1
    have integrable : IntervalIntegrable hilbertTangent volume 0 point.2 :=
      regular.continuous.intervalIntegrable 0 point.2
    exact ((binaryHilbertTranslation cusp (atInfinity (invertibleMatrix point.1))).intervalIntegral_comp_comm
      integrable).symm

end TernaryPeriodPolynomials.SphericalDetection.Helpers
