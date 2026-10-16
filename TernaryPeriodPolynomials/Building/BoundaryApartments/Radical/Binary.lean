module

public import TernaryPeriodPolynomials.Building.BoundaryApartments.LineCoboundary

@[expose] public section


open GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers

open Matrix MvPolynomial

theorem pderiv_bind_commutes (substitution : Fin 3 → Poly)
    (derivatives : ∀ index, pderiv 0 (substitution index) = bind₁ substitution (pderiv 0 (X index)))
    (polynomial : Poly) :
    pderiv 0 (bind₁ substitution polynomial) = bind₁ substitution (pderiv 0 polynomial) := by
  induction polynomial using MvPolynomial.induction_on with
  | C coefficient => simp
  | add first second first_eq second_eq => simp only [map_add, first_eq, second_eq]
  | mul_X polynomial index induction_hypothesis =>
    simp only [map_mul, pderiv_mul, map_add, bind₁_X_right, derivatives, induction_hypothesis]

theorem pderiv_radicalTranslation (index : Fin 3) (index_nonzero : index ≠ 0)
    (polynomial : Poly) :
    pderiv 0 (bind₁ ![X 0 - X index, X 1, X 2] polynomial) =
      bind₁ ![X 0 - X index, X 1, X 2] (pderiv 0 polynomial) := by
  apply pderiv_bind_commutes
  intro current
  fin_cases current <;> simp [index_nonzero]

theorem derivative_iterate_bind_commutes (substitution : Fin 3 → Poly)
    (derivatives : ∀ polynomial, pderiv 0 (bind₁ substitution polynomial) =
      bind₁ substitution (pderiv 0 polynomial))
    (iterations : ℕ) (polynomial : Poly) :
    ((fun value : Poly => pderiv 0 value)^[iterations]) (bind₁ substitution polynomial) =
      bind₁ substitution (((fun value : Poly => pderiv 0 value)^[iterations]) polynomial) := by
  induction iterations with
  | zero => rfl
  | succ iterations induction_hypothesis =>
    rw [Function.iterate_succ_apply', induction_hypothesis, derivatives,
      Function.iterate_succ_apply']

theorem bernoulliOperator_radicalTranslation (degree : ℕ) (index : Fin 3)
    (index_nonzero : index ≠ 0) (parameter polynomial : Poly)
    (parameter_fixed : bind₁ ![X 0 - X index, X 1, X 2] parameter = parameter) :
    bernoulliOperator degree parameter (bind₁ ![X 0 - X index, X 1, X 2] polynomial) =
      bind₁ ![X 0 - X index, X 1, X 2] (bernoulliOperator degree parameter polynomial) := by
  simp only [bernoulliOperator, map_sum, map_mul, map_pow, map_neg, bind₁_C_right,
    parameter_fixed]
  apply Finset.sum_congr rfl
  intro iterations _
  rw [derivative_iterate_bind_commutes _ (pderiv_radicalTranslation index index_nonzero)]

theorem derivative_zero_eval_binary (polynomial : Poly) (derivative_zero : pderiv 0 polynomial = 0)
    (first second third : ℂ) :
    polynomialValue polynomial first second third = polynomialValue polynomial 0 second third := by
  have derivative : Polynomial.derivative (firstVariablePolynomial polynomial second third) = 0 := by
    rw [← firstVariablePolynomial_pderiv, derivative_zero]
    simp [firstVariablePolynomial]
  have constant := Polynomial.eq_C_of_derivative_eq_zero derivative
  have evaluated := congrArg (Polynomial.eval first) constant
  have at_zero := congrArg (Polynomial.eval 0) constant
  simp only [Polynomial.eval_C] at evaluated at_zero
  rw [← at_zero] at evaluated
  simpa only [firstVariablePolynomial_eval] using evaluated

theorem radicalCocycle_contraction_binary (degree : ℕ) (first second : HomogeneousPoly degree)
    (cocycle_relation : radicalTranslation degree 1 second - second =
      radicalTranslation degree 2 first - first) :
    pderiv 0 (X 2 * bernoulliOperator degree (X 1) first.val -
      X 1 * bernoulliOperator degree (X 2) second.val) = 0 := by
  have first_homogeneous := bernoulliOperator_homogeneous (isHomogeneous_X ℂ 1) first.property
  let transformed_first : HomogeneousPoly degree :=
    ⟨bernoulliOperator degree (X 1) first.val, first_homogeneous⟩
  have relation := congrArg
    (fun polynomial : HomogeneousPoly degree => bernoulliOperator degree (X 1) polynomial.val)
    cocycle_relation
  simp only [Submodule.coe_sub,
    bernoulliRadical_difference degree 1 (by decide)] at relation
  change -X 1 * pderiv 0 second.val =
    bernoulliOperator degree (X 1)
      ((radicalTranslation degree 2 first).val - first.val) at relation
  have operator_sub (left right : Poly) : bernoulliOperator degree (X 1) (left - right) =
      bernoulliOperator degree (X 1) left - bernoulliOperator degree (X 1) right :=
    map_sub (bernoulliLinearMap degree (X 1)) left right
  rw [operator_sub] at relation
  have translated := bernoulliOperator_radicalTranslation degree 2 (by decide) (X 1) first.val
    (by simp)
  change bernoulliOperator degree (X 1) (radicalTranslation degree 2 first).val =
    (radicalTranslation degree 2 transformed_first).val at translated
  rw [translated] at relation
  have differentiated := congrArg (bernoulliOperator degree (X 2)) relation
  rw [bernoulliRadical_difference degree 2 (by decide) transformed_first] at differentiated
  have variable_derivative : pderiv 0 (X (1 : Fin 3) : Poly) = 0 := by simp
  rw [bernoulliOperator_mul_constant degree (X 2) (-X 1) _
    (by simp), ← derivative_bernoulliOperator degree (X 2) second.val (by simp)] at differentiated
  change -X 1 * pderiv 0 (bernoulliOperator degree (X 2) second.val) =
    -X 2 * pderiv 0 (bernoulliOperator degree (X 1) first.val) at differentiated
  simp only [map_sub, pderiv_mul, pderiv_X_of_ne (by decide : (2 : Fin 3) ≠ 0),
    variable_derivative, zero_mul, zero_add]
  linear_combination differentiated

end TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers
