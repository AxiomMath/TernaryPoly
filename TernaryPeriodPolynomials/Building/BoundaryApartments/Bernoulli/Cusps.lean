module

public import TernaryPeriodPolynomials.Building.BoundaryApartments.Mixed.RadicalCycle
public import TernaryPeriodPolynomials.Building.BoundaryApartments.SumBoundary

@[expose] public section


open GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers

open Matrix MvPolynomial

theorem derivative_eval_zero_of_line_zero (polynomial : Poly) (second third : ℂ)
    (line_zero : ∀ first, polynomialValue polynomial first second third = 0)
    (iterations : ℕ) (first : ℂ) :
    polynomialValue (((fun value : Poly => pderiv 0 value)^[iterations]) polynomial)
      first second third = 0 := by
  have restriction_zero : firstVariablePolynomial polynomial second third = 0 := by
    apply Polynomial.zero_of_eval_zero
    intro point
    rw [firstVariablePolynomial_eval]
    exact line_zero point
  rw [← firstVariablePolynomial_eval, firstVariablePolynomial_iterate, restriction_zero]
  have derivative_zero : (fun value : Polynomial ℂ => value.derivative) 0 = 0 :=
    Polynomial.derivative_zero
  rw [Function.iterate_fixed derivative_zero, Polynomial.eval_zero]

theorem bernoulliOperator_eval_zero_of_line_zero (degree : ℕ) (parameter polynomial : Poly)
    (second third : ℂ) (line_zero : ∀ first, polynomialValue polynomial first second third = 0)
    (first : ℂ) : polynomialValue (bernoulliOperator degree parameter polynomial) first second third = 0 := by
  unfold bernoulliOperator polynomialValue
  simp only [map_sum, map_mul]
  apply Finset.sum_eq_zero
  intro iterations _
  have zero_value := derivative_eval_zero_of_line_zero polynomial second third line_zero iterations first
  change eval ![first, second, third] _ * eval ![first, second, third] _ *
    polynomialValue (((fun value : Poly => pderiv 0 value)^[iterations]) polynomial)
      first second third = 0
  rw [zero_value, mul_zero]

theorem polynomialValue_firstFrame_upperCusp {degree : ℕ} {polynomial : HomogeneousPoly degree}
    (degree_positive : 0 < degree) (degree_even : Even degree)
    (solution : SymmetricSolution polynomial) (first second : ℂ) :
    polynomialValue (bind₁ ![X 2 - 2 * X 1, -X 0, X 0 - X 1] polynomial.val)
      first second (3 * second) = 0 := by
  rw [polynomialValue_bind]
  have coordinates : (fun index => polynomialValue
      (![X 2 - 2 * X 1, -X 0, X 0 - X 1] index) first second (3 * second)) =
        ![second, -first, first - second] := by
    funext index
    fin_cases index <;> simp [polynomialValue]
    ring
  rw [coordinates]
  have sum : first - second = -(second + -first) := by ring
  change polynomialValue polynomial.val second (-first) (first - second) = 0
  rw [sum]
  exact polynomialValue_sum_zero degree_positive degree_even solution second (-first)

theorem polynomialValue_secondFrame_upperCusp {degree : ℕ} {polynomial : HomogeneousPoly degree}
    (degree_positive : 0 < degree) (degree_even : Even degree)
    (solution : SymmetricSolution polynomial) (first second : ℂ) :
    polynomialValue (bind₁ ![X 2 - X 0, X 0 - 2 * X 1, -X 1] polynomial.val)
      first second (3 * second) = 0 := by
  rw [polynomialValue_bind]
  have coordinates : (fun index => polynomialValue
      (![X 2 - X 0, X 0 - 2 * X 1, -X 1] index) first second (3 * second)) =
        ![3 * second - first, first - 2 * second, -second] := by
    funext index
    fin_cases index <;> simp [polynomialValue]
  rw [coordinates]
  have sum : -second = -((3 * second - first) + (first - 2 * second)) := by ring
  change polynomialValue polynomial.val (3 * second - first) (first - 2 * second) (-second) = 0
  rw [sum]
  exact polynomialValue_sum_zero degree_positive degree_even solution _ _

theorem polynomialValue_thirdFrame_upperCusp {degree : ℕ} {polynomial : HomogeneousPoly degree}
    (degree_positive : 0 < degree) (degree_even : Even degree)
    (solution : SymmetricSolution polynomial) (first second : ℂ) :
    polynomialValue (bind₁ ![X 2 - 2 * X 1, X 1 - X 0, X 0 - 2 * X 1] polynomial.val)
      first second (3 * second) = 0 := by
  rw [polynomialValue_bind]
  have coordinates : (fun index => polynomialValue
      (![X 2 - 2 * X 1, X 1 - X 0, X 0 - 2 * X 1] index) first second (3 * second)) =
        ![second, second - first, first - 2 * second] := by
    funext index
    fin_cases index <;> simp [polynomialValue]
    ring
  rw [coordinates]
  have sum : first - 2 * second = -(second + (second - first)) := by ring
  change polynomialValue polynomial.val second (second - first) (first - 2 * second) = 0
  rw [sum]
  exact polynomialValue_sum_zero degree_positive degree_even solution _ _

theorem bernoulliObstruction_upperCusp {degree : ℕ} {polynomial : HomogeneousPoly degree}
    (degree_positive : 0 < degree) (degree_even : Even degree)
    (solution : SymmetricSolution polynomial) (first second : ℂ) :
    polynomialValue (bernoulliObstruction polynomial) first second (3 * second) = 0 := by
  have first_frame := polynomialValue_firstFrame_upperCusp degree_positive degree_even solution
  have second_frame := polynomialValue_secondFrame_upperCusp degree_positive degree_even solution
  have third_frame := polynomialValue_thirdFrame_upperCusp degree_positive degree_even solution
  have first_operator := bernoulliOperator_eval_zero_of_line_zero degree (X 1) _ second (3 * second)
    (fun point => first_frame point second) first
  have second_operator := bernoulliOperator_eval_zero_of_line_zero degree (X 2)
    (bind₁ ![X 2 - 2 * X 1, -X 0, X 0 - X 1] polynomial.val -
      bind₁ ![X 2 - X 0, X 0 - 2 * X 1, -X 1] polynomial.val +
      bind₁ ![X 2 - 2 * X 1, X 1 - X 0, X 0 - 2 * X 1] polynomial.val)
    second (3 * second) (by
      intro point
      change eval ![point, second, 3 * second] _ = 0
      simp only [map_add, map_sub]
      change polynomialValue _ point second (3 * second) -
        polynomialValue _ point second (3 * second) +
        polynomialValue _ point second (3 * second) = 0
      rw [first_frame, second_frame, third_frame]
      ring) first
  unfold bernoulliObstruction
  change eval ![first, second, 3 * second] _ = 0
  simp only [map_sub, map_mul, eval_X, Matrix.cons_val_two, Matrix.cons_val_one]
  change 3 * second * polynomialValue _ first second (3 * second) -
    second * polynomialValue _ first second (3 * second) = 0
  rw [first_operator, second_operator]
  ring

end TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers
