module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Cuspidal.TensorPolynomial

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

attribute [local instance] complexEndRationalAlgebra

variable {V : Type} [AddCommGroup V] [Module ℂ V] {index : Type} [Fintype index]

def cuspidalNilpotentPrimitive (cusp : CuspidalRepresentation) (operator : Module.End ℂ V)
    (cutoff : ℕ) (vector : cuspidalTensorValues cusp V) (parameter : ℝ) : cuspidalTensorValues cusp V :=
  ∑ power ∈ Finset.range cutoff, ((parameter : ℂ) ^ (power + 1) / (power + 1).factorial) •
    cuspidalTensorMap cusp (operator ^ power) vector

theorem cuspidalNilpotentPrimitive_apply (cusp : CuspidalRepresentation) (operator : Module.End ℂ V)
    (cutoff : ℕ) (vector : cuspidalTensorValues cusp V) (parameter : ℝ) (argument : BinaryAdelicGL) :
    (cuspidalNilpotentPrimitive cusp operator cutoff vector parameter).val argument =
      algebraicNilpotentPrimitive operator cutoff (vector.val argument) parameter := by
  simp only [cuspidalNilpotentPrimitive, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply,
    Pi.smul_apply, cuspidalTensorMap, LinearMap.coe_mk, AddHom.coe_mk, algebraicNilpotentPrimitive]

theorem cuspidalNilpotentPrimitive_hilbert (cusp : CuspidalRepresentation) (basis : Module.Basis index ℂ V)
    (operator : Module.End ℂ V) (cutoff : ℕ) (vector : cuspidalTensorValues cusp V) (parameter : ℝ) :
    cuspidalTensorHilbertEmbedding cusp basis (cuspidalNilpotentPrimitive cusp operator cutoff vector parameter) =
      finiteExponentialPrimitive
        (fun power => (basisHilbertCoefficientHom cusp basis operator ^ power)
          (cuspidalTensorHilbertEmbedding cusp basis vector)) cutoff parameter := by
  rw [← algebraicNilpotentPrimitive_eq_finite]
  simp only [cuspidalNilpotentPrimitive, map_sum, map_smul, cuspidalTensorHilbertEmbedding_map,
    algebraicNilpotentPrimitive]
  apply Finset.sum_congr rfl
  intro power _
  congr 1
  exact LinearMap.congr_fun ((basisHilbertCoefficientHom cusp basis).map_pow operator power)
    (cuspidalTensorHilbertEmbedding cusp basis vector)

theorem cuspidalNilpotentPrimitive_finiteLevel (cusp : CuspidalRepresentation) (operator : Module.End ℂ V)
    (cutoff : ℕ) (vector : cuspidalTensorValues cusp V) (fixed : vector ∈ cuspidalTensorFiniteLevel cusp V)
    (parameter : ℝ) : cuspidalNilpotentPrimitive cusp operator cutoff vector parameter ∈ cuspidalTensorFiniteLevel cusp V := by
  exact (cuspidalTensorFiniteLevel cusp V).sum_mem (fun power _ =>
    (cuspidalTensorFiniteLevel cusp V).smul_mem _ (cuspidalTensorMap_finiteLevel cusp (operator ^ power) vector fixed))

theorem cuspidalNilpotentPrimitive_analytic (cusp : CuspidalRepresentation) (basis : Module.Basis index ℂ V)
    (operator : Module.End ℂ V) (cutoff : ℕ) (vector : cuspidalTensorValues cusp V) (center : ℝ) : AnalyticAt ℝ
      (fun point : BinaryRealMatrix × ℝ => binaryHilbertTranslation cusp (atInfinity (invertibleMatrix point.1))
        (cuspidalTensorHilbertEmbedding cusp basis (cuspidalNilpotentPrimitive cusp operator cutoff vector point.2)))
      (1, center) := by
  apply cuspidalTensorPolynomial_analytic cusp basis (fun power => cuspidalTensorMap cusp (operator ^ power) vector)
    (fun power parameter => (parameter : ℂ) ^ (power + 1) / (power + 1).factorial) cutoff center
  intro power
  have regular : ContDiff ℝ ⊤ (fun parameter : ℝ => (parameter : ℂ) ^ (power + 1) / (power + 1).factorial) := by
    exact (Complex.ofRealCLM.contDiff.pow (power + 1)).div_const _
  exact regular.contDiffAt.analyticAt

end TernaryPeriodPolynomials.SphericalDetection.Helpers
