module

public import TernaryPeriodPolynomials.Building.BoundaryApartments.PolynomialIdentities

@[expose] public section


open GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers

open Matrix Homogeneous MvPolynomial

theorem bernoulliOperator_eval_parameter_zero (degree : ℕ) (parameter polynomial : Poly)
    (coordinates : Fin 3 → ℂ) (parameter_zero : eval coordinates parameter = 0) :
    eval coordinates (bernoulliOperator degree parameter polynomial) =
      eval coordinates polynomial := by
  classical
  unfold bernoulliOperator
  simp only [map_sum]
  rw [Finset.sum_eq_single 0]
  · simp [bernoulli_zero]
  · intro iterations _ iterations_nonzero
    simp [parameter_zero, zero_pow iterations_nonzero]
  · intro zero_not_in_range
    exact False.elim (zero_not_in_range (Finset.mem_range.mpr (Nat.zero_lt_succ degree)))

theorem bernoulliObstruction_goodBoundary {degree : ℕ} {polynomial : HomogeneousPoly degree}
    (solution : SymmetricSolution polynomial) (first third : ℂ) :
    polynomialValue (bernoulliObstruction polynomial) first 0 third = 0 := by
  have parameter_zero : eval ![first, (0 : ℂ), third] (X (1 : Fin 3)) = 0 := by simp
  have evaluated := bernoulliOperator_eval_parameter_zero degree (X 1)
    (bind₁ ![X 2 - 2 * X 1, -X 0, X 0 - X 1] polynomial.val)
    ![first, 0, third] parameter_zero
  unfold polynomialValue bernoulliObstruction
  simp only [map_sub, map_mul, eval_X, Matrix.cons_val_two, Matrix.cons_val_one,
    Matrix.cons_val_zero, Matrix.vecHead, Matrix.vecTail, zero_mul, sub_zero]
  rw [evaluated]
  change third * polynomialValue (bind₁ ![X 2 - 2 * X 1, -X 0, X 0 - X 1]
    polynomial.val) first 0 third = 0
  rw [polynomialValue_bind]
  have coordinates : (fun index => polynomialValue
      (![X 2 - 2 * X 1, -X 0, X 0 - X 1] index) first 0 third) =
      ![third, -first, first] := by
    funext index
    fin_cases index <;> simp [polynomialValue]
  rw [coordinates]
  change third * polynomialValue polynomial.val third (-first) first = 0
  rw [polynomialValue_cyclic solution (-first) first third,
    polynomialValue_swap_first solution first (-first) third,
    polynomialValue_opposite_zero solution, mul_zero]

end TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers
