module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Cuspidal.NilpotentPrimitive

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

attribute [local instance] complexEndRationalAlgebra

variable {V : Type} [AddCommGroup V] [Module ℂ V] {index : Type} [Fintype index]

theorem cuspidalNilpotentCocycle_exists_of_one (cusp : CuspidalRepresentation) (basis : Module.Basis index ℂ V)
    (operator : Module.End ℂ V) (cutoff : ℕ) (nilpotent : operator ^ (cutoff + 1) = 0)
    (action : ℝ → Module.End ℂ (cuspidalTensorValues cusp V))
    (hilbertAction : ℝ → (index → cusp.H) →L[ℝ] (index → cusp.H))
    (intertwines : ∀ parameter vector, cuspidalTensorHilbertEmbedding cusp basis (action parameter vector) =
      hilbertAction parameter (cuspidalTensorHilbertEmbedding cusp basis vector))
    (exponential : ∀ parameter vector, hilbertAction parameter vector =
      IsNilpotent.exp ((parameter : ℂ) • basisHilbertCoefficientHom cusp basis operator) vector)
    (action_add : ∀ first second vector, hilbertAction (first + second) vector = hilbertAction first (hilbertAction second vector))
    (vector : cuspidalTensorValues cusp V) (fixed : vector ∈ cuspidalTensorFiniteLevel cusp V) :
    ∃ cycle : ℝ → cuspidalTensorValues cusp V,
      cycle 0 = 0 ∧ cycle 1 = vector ∧ (∀ parameter, cycle parameter ∈ cuspidalTensorFiniteLevel cusp V) ∧
      ContDiff ℝ (↑(⊤ : ℕ∞)) (fun parameter => cuspidalTensorHilbertEmbedding cusp basis (cycle parameter)) ∧
      (∀ center : ℝ, AnalyticAt ℝ
        (fun point : BinaryRealMatrix × ℝ => binaryHilbertTranslation cusp (atInfinity (invertibleMatrix point.1))
          (cuspidalTensorHilbertEmbedding cusp basis (cycle point.2))) (1, center)) ∧
      ∀ first second, cycle (first + second) = action first (cycle second) + cycle first := by
  let average := nilpotentAverageEquiv operator ⟨cutoff + 1, nilpotent⟩ cutoff
  let tangent := cuspidalTensorMap cusp average.symm.toLinearMap vector
  let cycle := cuspidalNilpotentPrimitive cusp operator (cutoff + 1) tangent
  have tangent_fixed : tangent ∈ cuspidalTensorFiniteLevel cusp V :=
    cuspidalTensorMap_finiteLevel cusp average.symm.toLinearMap vector fixed
  have hilbert_nilpotent : basisHilbertCoefficientHom cusp basis operator ^ (cutoff + 1) = 0 := by
    rw [← map_pow, nilpotent, map_zero]
  refine ⟨cycle, ?_, ?_, ?_, ?_, cuspidalNilpotentPrimitive_analytic cusp basis operator (cutoff + 1) tangent, ?_⟩
  · apply Subtype.ext
    funext argument
    exact (cuspidalNilpotentPrimitive_apply cusp operator (cutoff + 1) tangent 0 argument).trans
      (algebraicNilpotentPrimitive_zero operator (cutoff + 1) (tangent.val argument))
  · apply Subtype.ext
    funext argument
    rw [cuspidalNilpotentPrimitive_apply, algebraicNilpotentPrimitive_one]
    exact average.apply_symm_apply (vector.val argument)
  · exact cuspidalNilpotentPrimitive_finiteLevel cusp operator (cutoff + 1) tangent tangent_fixed
  · have regular := finiteExponentialPrimitive_contDiff
      (fun power => (basisHilbertCoefficientHom cusp basis operator ^ power)
        (cuspidalTensorHilbertEmbedding cusp basis tangent)) (cutoff + 1)
    simpa only [cycle, cuspidalNilpotentPrimitive_hilbert] using regular
  · intro first second
    apply cuspidalTensorHilbertEmbedding_injective cusp basis
    rw [map_add, intertwines]
    simp only [cycle, cuspidalNilpotentPrimitive_hilbert]
    exact finiteExponentialPrimitive_cocycle (basisHilbertCoefficientHom cusp basis operator) (cutoff + 1)
      hilbert_nilpotent hilbertAction exponential action_add (cuspidalTensorHilbertEmbedding cusp basis tangent) first second

end TernaryPeriodPolynomials.SphericalDetection.Helpers
