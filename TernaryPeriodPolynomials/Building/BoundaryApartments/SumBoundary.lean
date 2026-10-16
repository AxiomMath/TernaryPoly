module

public import TernaryPeriodPolynomials.Building.BoundaryApartments.DetectionAlgebra

@[expose] public section


open GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers

open Matrix MvPolynomial

theorem polynomialValue_neg_even {degree : ℕ} (polynomial : HomogeneousPoly degree)
    (degree_even : Even degree) (first second third : ℂ) :
    polynomialValue polynomial.val (-first) (-second) (-third) =
      polynomialValue polynomial.val first second third := by
  rw [polynomialValue_neg, degree_even.neg_one_pow, one_mul]

theorem sumBoundary_first_shear {degree : ℕ} {polynomial : HomogeneousPoly degree}
    (solution : SymmetricSolution polynomial) (degree_even : Even degree) (first second : ℂ) :
    polynomialValue polynomial.val first second (-(first + second)) =
      polynomialValue polynomial.val (first + second) second (-(first + 2 * second)) := by
  have first_norm := polynomialValue_norm_first solution (-(first + second)) second first
  have second_norm := polynomialValue_norm_last solution (-(first + 2 * second)) (-second) first
  have first_reorder : polynomialValue polynomial.val (-(first + second)) second first =
      polynomialValue polynomial.val first second (-(first + second)) := by
    rw [polynomialValue_swap_first solution, polynomialValue_swap_last solution,
      polynomialValue_swap_first solution]
  have negative_pair : polynomialValue polynomial.val (-(first + 2 * second)) (-first) (-(first + second)) =
      polynomialValue polynomial.val (first + 2 * second) (first + second) first := by
    rw [polynomialValue_neg_even polynomial degree_even, polynomialValue_swap_last solution]
  have coordinates_one : -(first + second) - second = -(first + 2 * second) := by ring
  have coordinates_two : second - -(first + second) = first + 2 * second := by ring
  have coordinates_three : - -(first + second) = first + second := by ring
  have coordinates_four : -second - first = -(first + second) := by ring
  have coordinates_five : first - -second = first + second := by ring
  rw [first_reorder, coordinates_one, coordinates_two, coordinates_three] at first_norm
  rw [coordinates_four, coordinates_five, neg_neg, negative_pair] at second_norm
  rw [polynomialValue_swap_first solution (-(first + 2 * second)) (-second) first] at first_norm
  have final_reorder : polynomialValue polynomial.val (-(first + 2 * second)) (first + second) second =
      polynomialValue polynomial.val (first + second) second (-(first + 2 * second)) := by
    rw [polynomialValue_swap_first solution, polynomialValue_swap_last solution]
  rw [final_reorder] at second_norm
  linear_combination first_norm - second_norm

theorem sumBoundary_second_shear {degree : ℕ} {polynomial : HomogeneousPoly degree}
    (solution : SymmetricSolution polynomial) (degree_even : Even degree) (first second : ℂ) :
    polynomialValue polynomial.val first second (-(first + second)) =
      polynomialValue polynomial.val first (first + second) (-(2 * first + second)) := by
  have swapped := sumBoundary_first_shear solution degree_even second first
  have sum_comm : second + first = first + second := by ring
  have doubled_comm : second + 2 * first = 2 * first + second := by ring
  rw [sum_comm, doubled_comm, polynomialValue_swap_first solution first second,
    polynomialValue_swap_first solution first (first + second)] at swapped
  exact swapped

def sumBoundaryPolynomial (polynomial : Poly) (parameter : ℂ) : Polynomial ℂ :=
  eval₂Hom Polynomial.C
    ![Polynomial.X, Polynomial.C parameter, -(Polynomial.X + Polynomial.C parameter)] polynomial

theorem sumBoundaryPolynomial_eval (polynomial : Poly) (parameter point : ℂ) :
    Polynomial.eval point (sumBoundaryPolynomial polynomial parameter) =
      polynomialValue polynomial point parameter (-(point + parameter)) := by
  unfold sumBoundaryPolynomial
  change (Polynomial.evalRingHom point) ((eval₂Hom Polynomial.C
    ![Polynomial.X, Polynomial.C parameter, -(Polynomial.X + Polynomial.C parameter)]) polynomial) = _
  rw [MvPolynomial.map_eval₂Hom]
  have coefficients : (Polynomial.evalRingHom point).comp Polynomial.C = RingHom.id ℂ := by
    ext coefficient
    simp
  have coordinates : (fun index => (Polynomial.evalRingHom point)
      (![Polynomial.X, Polynomial.C parameter, -(Polynomial.X + Polynomial.C parameter)] index)) =
        ![point, parameter, -(point + parameter)] := by
    funext index
    fin_cases index <;> simp
  rw [coefficients, coordinates]
  rfl

theorem polynomialValue_origin_positive {degree : ℕ} (polynomial : HomogeneousPoly degree)
    (degree_positive : 0 < degree) : polynomialValue polynomial.val 0 0 0 = 0 := by
  have scaled := homogeneousValue_scale polynomial 0 ![0, 0, 0]
  have coordinates : (fun index : Fin 3 => (0 : ℂ) * (![0, 0, 0] index)) = ![0, 0, 0] := by
    funext index
    fin_cases index <;> simp
  rw [coordinates, zero_pow (Nat.ne_zero_of_lt degree_positive), zero_mul] at scaled
  exact scaled

theorem polynomialValue_sum_zero {degree : ℕ} {polynomial : HomogeneousPoly degree}
    (_degree_positive : 0 < degree) (degree_even : Even degree)
    (solution : SymmetricSolution polynomial) (first second : ℂ) :
    polynomialValue polynomial.val first second (-(first + second)) = 0 := by
  have first_independent (parameter : ℂ) (parameter_nonzero : parameter ≠ 0) (point : ℂ) :
      polynomialValue polynomial.val point parameter (-(point + parameter)) =
        polynomialValue polynomial.val 0 parameter (-parameter) := by
    have periodic : ∀ point,
        (sumBoundaryPolynomial polynomial.val parameter).eval (point + parameter) =
          (sumBoundaryPolynomial polynomial.val parameter).eval point := by
      intro point
      rw [sumBoundaryPolynomial_eval, sumBoundaryPolynomial_eval]
      have coordinates : point + parameter + parameter = point + 2 * parameter := by ring
      rw [coordinates]
      exact (sumBoundary_first_shear solution degree_even point parameter).symm
    have constant := polynomial_periodic_eval_constant (sumBoundaryPolynomial polynomial.val parameter)
      parameter parameter_nonzero periodic point
    simpa only [sumBoundaryPolynomial_eval, zero_add] using constant
  by_cases second_zero : second = 0
  · subst second
    simp only [add_zero]
    rw [polynomialValue_swap_last solution, polynomialValue_swap_first solution]
    simpa only [neg_neg] using polynomialValue_opposite_zero solution (-first) 0
  · rw [first_independent second second_zero first]
    rw [polynomialValue_cyclic solution second (-second) 0]
    exact polynomialValue_opposite_zero solution second 0

end TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers
