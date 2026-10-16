module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Real.NilpotentCocycle

@[expose] public section


noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

attribute [local instance] complexEndRationalAlgebra

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in
theorem finiteExponentialPrimitive_contDiff (vectors : ℕ → E) (cutoff : ℕ) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (finiteExponentialPrimitive vectors cutoff) := by
  unfold finiteExponentialPrimitive
  fun_prop

theorem finiteExponentialPrimitive_cocycle (operator : Module.End ℂ E) (cutoff : ℕ)
    (nilpotent : operator ^ cutoff = 0) (action : ℝ → E →L[ℝ] E)
    (exponential : ∀ parameter vector, action parameter vector = IsNilpotent.exp ((parameter : ℂ) • operator) vector)
    (action_add : ∀ first second vector, action (first + second) vector = action first (action second vector))
    (vector : E) (first second : ℝ) :
    finiteExponentialPrimitive (fun power => (operator ^ power) vector) cutoff (first + second) =
      action first (finiteExponentialPrimitive (fun power => (operator ^ power) vector) cutoff second) +
        finiteExponentialPrimitive (fun power => (operator ^ power) vector) cutoff first := by
  let primitive := finiteExponentialPrimitive (fun power => (operator ^ power) vector) cutoff
  have derivative (point : ℝ) : HasDerivAt primitive (action point vector) point := by
    rw [exponential, nilpotentExponential_real_parameter operator cutoff nilpotent]
    exact finiteExponentialPrimitive_hasDerivAt _ cutoff point
  have difference_derivative (point : ℝ) : HasDerivAt
      (fun sample => primitive (first + sample) - action first (primitive sample)) 0 point := by
    have shifted := (derivative (first + point)).scomp point ((hasDerivAt_id point).const_add first)
    have mapped := (action first).hasFDerivAt.comp_hasDerivAt point (derivative point)
    convert shifted.sub mapped using 1
    · rfl
    · simp only [one_smul, action_add, sub_self]
  have constant := is_const_of_deriv_eq_zero (fun point => (difference_derivative point).differentiableAt)
    (fun point => (difference_derivative point).deriv)
  have equality := constant second 0
  have origin : primitive 0 = 0 := finiteExponentialPrimitive_zero _ _
  rw [add_zero, origin, map_zero, sub_zero] at equality
  change primitive (first + second) = action first (primitive second) + primitive first
  linear_combination (norm := abel) equality

theorem additiveNilpotentCocycle_exists_of_one (operator : Module.End ℂ E) (cutoff : ℕ)
    (nilpotent : operator ^ (cutoff + 1) = 0) (action : ℝ → E →L[ℝ] E)
    (exponential : ∀ parameter vector, action parameter vector = IsNilpotent.exp ((parameter : ℂ) • operator) vector)
    (action_add : ∀ first second vector, action (first + second) vector = action first (action second vector))
    (vector : E) :
    ∃ cycle : ℝ → E, cycle 0 = 0 ∧ cycle 1 = vector ∧ ContDiff ℝ (↑(⊤ : ℕ∞)) cycle ∧
      ∀ first second, cycle (first + second) = action first (cycle second) + cycle first := by
  let tangent := (nilpotentAverageEquiv operator ⟨cutoff + 1, nilpotent⟩ cutoff).symm vector
  refine ⟨finiteExponentialPrimitive (fun power => (operator ^ power) tangent) (cutoff + 1),
    finiteExponentialPrimitive_zero _ _, ?_, finiteExponentialPrimitive_contDiff _ _, ?_⟩
  · rw [finiteExponentialPrimitive_one_average]
    exact (nilpotentAverageEquiv operator ⟨cutoff + 1, nilpotent⟩ cutoff).apply_symm_apply vector
  · exact finiteExponentialPrimitive_cocycle operator (cutoff + 1) nilpotent action exponential action_add tangent

end TernaryPeriodPolynomials.SphericalDetection.Helpers
