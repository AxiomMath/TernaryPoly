module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Real.NilpotentInterpolation

@[expose] public section


noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

attribute [local instance] complexEndRationalAlgebra

variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def algebraicNilpotentPrimitive (operator : Module.End ℂ V) (cutoff : ℕ) (vector : V) (parameter : ℝ) : V :=
  ∑ power ∈ Finset.range cutoff, ((parameter : ℂ) ^ (power + 1) / (power + 1).factorial) • (operator ^ power) vector

theorem algebraicNilpotentPrimitive_zero (operator : Module.End ℂ V) (cutoff : ℕ) (vector : V) :
    algebraicNilpotentPrimitive operator cutoff vector 0 = 0 := by
  simp [algebraicNilpotentPrimitive]

theorem algebraicNilpotentPrimitive_one (operator : Module.End ℂ V) (cutoff : ℕ) (vector : V) :
    algebraicNilpotentPrimitive operator cutoff vector 1 = nilpotentExponentialAverage operator cutoff vector := by
  rw [algebraicNilpotentPrimitive, nilpotentExponentialAverage, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro power _
  rw [rationalEnd_smul_apply]
  congr 1
  push_cast
  simp

theorem algebraicNilpotentPrimitive_map (linear : V →ₗ[ℂ] W)
    (first : Module.End ℂ V) (second : Module.End ℂ W)
    (intertwines : ∀ vector, linear (first vector) = second (linear vector))
    (cutoff : ℕ) (vector : V) (parameter : ℝ) :
    linear (algebraicNilpotentPrimitive first cutoff vector parameter) =
      algebraicNilpotentPrimitive second cutoff (linear vector) parameter := by
  have powers (power : ℕ) (vector : V) : linear ((first ^ power) vector) = (second ^ power) (linear vector) := by
    induction power with
    | zero => rfl
    | succ power hypothesis =>
      rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, intertwines, hypothesis]
  simp only [algebraicNilpotentPrimitive, map_sum, map_smul, powers]

theorem algebraicNilpotentPrimitive_eq_finite {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
    (operator : Module.End ℂ E) (cutoff : ℕ) (vector : E) (parameter : ℝ) :
    algebraicNilpotentPrimitive operator cutoff vector parameter =
      finiteExponentialPrimitive (fun power => (operator ^ power) vector) cutoff parameter := by
  rw [algebraicNilpotentPrimitive, finiteExponentialPrimitive]
  apply Finset.sum_congr rfl
  intro power _
  rw [← IsScalarTower.algebraMap_smul ℂ (parameter ^ (power + 1) / (power + 1).factorial)]
  congr 1
  push_cast
  rfl

end TernaryPeriodPolynomials.SphericalDetection.Helpers
