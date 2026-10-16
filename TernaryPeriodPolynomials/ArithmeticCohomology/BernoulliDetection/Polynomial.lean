module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BernoulliDetection.Helpers
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.MvPolynomial.Polynomial

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic
open MvPolynomial

namespace TernaryPeriodPolynomials.PolynomialBernoulliDetection.Helpers

theorem polynomial_periodic_constant (polynomial : Polynomial ℂ) (shift : ℂ)
    (shift_ne : shift ≠ 0)
    (periodic : ∀ value, polynomial.eval (value + shift) = polynomial.eval value) :
    polynomial = Polynomial.C (polynomial.eval 0) := by
  have values : ∀ index : ℕ, polynomial.eval ((index : ℂ) * shift) = polynomial.eval 0 := by
    intro index
    induction index with
    | zero => simp
    | succ index induction_hypothesis =>
      simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul, periodic] using
        induction_hypothesis
  apply Polynomial.eq_of_infinite_eval_eq
  have injective : Function.Injective (fun index : ℕ => (index : ℂ) * shift) := by
    intro left right equality
    exact Nat.cast_injective (mul_right_cancel₀ shift_ne equality)
  apply (Set.infinite_range_of_injective injective).mono
  rintro value ⟨index, rfl⟩
  simpa using values index

theorem eval_bind (substitution : Fin 3 → Poly) (polynomial : Poly)
    (values : Fin 3 → ℂ) :
    eval values (bind₁ substitution polynomial) =
      eval (fun index => eval values (substitution index)) polynomial :=
  eval₂Hom_bind₁ (RingHom.id ℂ) values substitution polynomial

theorem homogeneous_eval_scale {degree : ℕ} (polynomial : HomogeneousPoly degree)
    (scalar : ℂ) (values : Fin 3 → ℂ) :
    eval (fun index => scalar * values index) polynomial.val =
      scalar ^ degree * eval values polynomial.val := by
  classical
  rw [eval_eq, eval_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro monomial membership
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
    ← polynomial.property.degree_eq_sum_deg_support membership]
  ring

theorem symmetric_eval {degree : ℕ} (polynomial : HomogeneousPoly degree)
    (symmetric : SymmetricSolution polynomial) (permutation : Equiv.Perm (Fin 3))
    (values : Fin 3 → ℂ) :
    eval (fun index => values (permutation index)) polynomial.val =
      eval values polynomial.val := by
  have equality := congrArg (eval values) (symmetric.1 permutation)
  simpa only [eval_bind, eval_X] using equality

theorem symmetric_eval_swap_first {degree : ℕ} (polynomial : HomogeneousPoly degree)
    (symmetric : SymmetricSolution polynomial) (first second third : ℂ) :
    eval ![second, first, third] polynomial.val =
      eval ![first, second, third] polynomial.val := by
  have coordinates : (fun index => ![first, second, third] ((Equiv.swap 0 1) index)) =
      ![second, first, third] := by
    ext index
    fin_cases index <;> simp [Equiv.swap_apply_def]
  simpa only [coordinates] using
    symmetric_eval polynomial symmetric (Equiv.swap 0 1) ![first, second, third]

theorem symmetric_eval_swap_last {degree : ℕ} (polynomial : HomogeneousPoly degree)
    (symmetric : SymmetricSolution polynomial) (first second third : ℂ) :
    eval ![first, third, second] polynomial.val =
      eval ![first, second, third] polynomial.val := by
  have coordinates : (fun index => ![first, second, third] ((Equiv.swap 1 2) index)) =
      ![first, third, second] := by
    ext index
    fin_cases index <;> simp [Equiv.swap_apply_def]
  simpa only [coordinates] using
    symmetric_eval polynomial symmetric (Equiv.swap 1 2) ![first, second, third]

theorem symmetric_eval_norm_first {degree : ℕ} (polynomial : HomogeneousPoly degree)
    (symmetric : SymmetricSolution polynomial) (first second third : ℂ) :
    eval ![first, second, third] polynomial.val +
      eval ![-second, first - second, third] polynomial.val +
      eval ![second - first, -first, third] polynomial.val = 0 := by
  have equality := congrArg (eval ![first, second, third]) symmetric.2
  have first_coordinates :
      (fun index => eval ![first, second, third] (![-X 1, X 0 - X 1, X 2] index)) =
        ![-second, first - second, third] := by
    ext index
    fin_cases index <;> simp
  have second_coordinates :
      (fun index => eval ![first, second, third] (![X 1 - X 0, -X 0, X 2] index)) =
        ![second - first, -first, third] := by
    ext index
    fin_cases index <;> simp
  simpa only [map_add, eval_bind, first_coordinates, second_coordinates, map_zero] using equality

theorem symmetric_eval_norm_last {degree : ℕ} (polynomial : HomogeneousPoly degree)
    (symmetric : SymmetricSolution polynomial) (first second third : ℂ) :
    eval ![first, second, third] polynomial.val +
      eval ![first, -third, second - third] polynomial.val +
      eval ![first, third - second, -second] polynomial.val = 0 := by
  have equality := symmetric_eval_norm_first polynomial symmetric second third first
  have cyclic (first second third : ℂ) :
      eval ![second, third, first] polynomial.val =
        eval ![first, second, third] polynomial.val := by
    rw [symmetric_eval_swap_last polynomial symmetric second first third,
      symmetric_eval_swap_first polynomial symmetric first second third]
  simpa only [cyclic] using equality

theorem symmetric_eval_cyclic {degree : ℕ} (polynomial : HomogeneousPoly degree)
    (symmetric : SymmetricSolution polynomial) (first second third : ℂ) :
    eval ![second, third, first] polynomial.val =
      eval ![first, second, third] polynomial.val := by
  rw [symmetric_eval_swap_last polynomial symmetric second first third,
    symmetric_eval_swap_first polynomial symmetric first second third]

theorem homogeneous_eval_neg {degree : ℕ} (polynomial : HomogeneousPoly degree)
    (first second third : ℂ) :
    eval ![-first, -second, -third] polynomial.val =
      (-1 : ℂ) ^ degree * eval ![first, second, third] polynomial.val := by
  have coordinates : (fun index => (-1 : ℂ) * ![first, second, third] index) =
      ![-first, -second, -third] := by
    ext index
    fin_cases index <;> simp
  simpa only [coordinates] using homogeneous_eval_scale polynomial (-1) ![first, second, third]

theorem symmetric_opposite_period {degree : ℕ} (polynomial : HomogeneousPoly degree)
    (symmetric : SymmetricSolution polynomial) (first second : ℂ) :
    eval ![first, -first, second] polynomial.val =
      eval ![first + second, -(first + second), second] polynomial.val := by
  let value (first second third : ℂ) := eval ![first, second, third] polynomial.val
  let sign := (-1 : ℂ) ^ degree
  have sign_ne : sign ≠ 0 := pow_ne_zero _ (by norm_num)
  have norm_first := symmetric_eval_norm_first polynomial symmetric (-first-second) 0 first
  have norm_last_one := symmetric_eval_norm_last polynomial symmetric (-first) (-second) first
  have norm_last_two := symmetric_eval_norm_last polynomial symmetric (-first-second) (-second) first
  have norm_last_three := symmetric_eval_norm_last polynomial symmetric (-first-second) (-first) (-first)
  simp only [neg_zero, sub_zero, zero_sub, neg_sub, neg_neg, sub_neg_eq_add]
    at norm_first norm_last_one norm_last_two norm_last_three
  simp only [sub_eq_add_neg, add_comm second first, neg_add_cancel]
    at norm_first norm_last_one norm_last_two norm_last_three
  change value (-first-second) 0 first + value 0 (-first-second) first +
    value (first+second) (first+second) first = 0 at norm_first
  change value (-first) (-second) first + value (-first) (-first) (-second-first) +
    value (-first) (first+second) second = 0 at norm_last_one
  change value (-first-second) (-second) first + value (-first-second) (-first) (-second-first) +
    value (-first-second) (first+second) second = 0 at norm_last_two
  change value (-first-second) (-first) (-first) + value (-first-second) first 0 +
    value (-first-second) 0 first = 0 at norm_last_three
  have first_term : value (-first) (-second) first = sign * value first (-first) second := by
    have equality := homogeneous_eval_neg polynomial first second (-first)
    simp only [neg_neg] at equality
    rw [symmetric_eval_swap_last polynomial symmetric first (-first) second] at equality
    exact equality
  have second_term : value (-first) (-first) (-second-first) =
      value (-first-second) (-first) (-first) := by
    have equality := symmetric_eval_cyclic polynomial symmetric (-first-second) (-first) (-first)
    simpa only [sub_eq_add_neg, add_comm] using equality
  have third_term : value (-first) (first+second) second =
      sign * value (-first-second) (-second) first := by
    have equality := homogeneous_eval_neg polynomial (-first-second) (-second) first
    simp only [neg_neg, neg_sub, sub_neg_eq_add, add_comm second first] at equality
    rw [symmetric_eval_cyclic polynomial symmetric (-first) (first+second) second] at equality
    exact equality
  have fourth_term : sign * value (-first-second) (-first) (-second-first) =
      value (first+second) (first+second) first := by
    have equality := homogeneous_eval_neg polynomial (-first-second) (-first) (-second-first)
    simp only [neg_neg, neg_sub, sub_neg_eq_add, add_comm second first] at equality
    rw [symmetric_eval_swap_last polynomial symmetric (first+second) (first+second) first]
      at equality
    exact equality.symm
  have fifth_term : value (-first-second) (first+second) second =
      value (first+second) (-(first+second)) second := by
    dsimp only [value]
    rw [symmetric_eval_swap_first polynomial symmetric (first+second) (-first-second) second]
    simp only [neg_add, sub_eq_add_neg]
  have sixth_term : value (-first-second) first 0 = value 0 (-first-second) first := by
    exact symmetric_eval_cyclic polynomial symmetric 0 (-first-second) first
  apply mul_left_cancel₀ sign_ne
  change sign * value first (-first) second = sign * value (first+second) (-(first+second)) second
  rw [first_term, second_term, third_term] at norm_last_one
  rw [fifth_term] at norm_last_two
  rw [sixth_term] at norm_last_three
  linear_combination norm_last_one - sign * norm_last_two - norm_last_three + norm_first + fourth_term

theorem symmetric_opposite_vanishes {degree : ℕ} (polynomial : HomogeneousPoly degree)
    (symmetric : SymmetricSolution polynomial) (first second : ℂ) :
    eval ![first, -first, second] polynomial.val = 0 := by
  let parameterPolynomial (second : ℂ) : Polynomial ℂ :=
    eval₂Hom Polynomial.C ![Polynomial.X, -Polynomial.X, Polynomial.C second] polynomial.val
  have evaluate (parameter second : ℂ) :
      (parameterPolynomial second).eval parameter =
        eval ![parameter, -parameter, second] polynomial.val := by
    let evaluation := (Polynomial.evalRingHom parameter).comp
      (eval₂Hom Polynomial.C ![Polynomial.X, -Polynomial.X, Polynomial.C second])
    have equality : evaluation = eval ![parameter, -parameter, second] := by
      apply ringHom_ext
      · intro coefficient
        simp [evaluation]
      · intro index
        fin_cases index <;> simp [evaluation]
    exact congrArg (fun hom => hom polynomial.val) equality
  have origin (second : ℂ) : eval ![0, 0, second] polynomial.val = 0 := by
    have equality := symmetric_eval_norm_first polynomial symmetric 0 0 second
    simp only [neg_zero, sub_self] at equality
    linear_combination equality / 3
  have nonzero_second (first second : ℂ) (nonzero : second ≠ 0) :
      eval ![first, -first, second] polynomial.val = 0 := by
    have constant := polynomial_periodic_constant (parameterPolynomial second) second nonzero
      (fun parameter => by
        simp only [evaluate]
        exact (symmetric_opposite_period polynomial symmetric parameter second).symm)
    have equality := congrArg (fun polynomial : Polynomial ℂ => polynomial.eval first) constant
    simpa only [evaluate, Polynomial.eval_C, neg_zero, origin] using equality
  by_cases nonzero : second ≠ 0
  · exact nonzero_second first second nonzero
  · have second_zero : second = 0 := not_ne_iff.mp nonzero
    subst second
    let finalPolynomial : Polynomial ℂ :=
      eval₂Hom Polynomial.C ![Polynomial.C first, Polynomial.C (-first), Polynomial.X] polynomial.val
    have final_evaluate (parameter : ℂ) :
        finalPolynomial.eval parameter = eval ![first, -first, parameter] polynomial.val := by
      let evaluation := (Polynomial.evalRingHom parameter).comp
        (eval₂Hom Polynomial.C ![Polynomial.C first, Polynomial.C (-first), Polynomial.X])
      have equality : evaluation = eval ![first, -first, parameter] := by
        apply ringHom_ext
        · intro coefficient
          simp [evaluation]
        · intro index
          fin_cases index <;> simp [evaluation]
      exact congrArg (fun hom => hom polynomial.val) equality
    have final_zero : finalPolynomial = 0 := by
      apply Polynomial.eq_of_infinite_eval_eq
      have infinite : (Set.univ \ {0} : Set ℂ).Infinite :=
        Set.infinite_univ.sdiff (Set.finite_singleton 0)
      apply infinite.mono
      intro parameter membership
      have parameter_ne : parameter ≠ 0 := by simpa using membership.2
      simpa only [Set.mem_ofPred_eq, final_evaluate, Polynomial.eval_zero] using
        nonzero_second first parameter parameter_ne
    simpa only [final_evaluate, Polynomial.eval_zero] using
      congrArg (fun polynomial : Polynomial ℂ => polynomial.eval 0) final_zero

theorem symmetric_opposite_substitution {degree : ℕ} (polynomial : HomogeneousPoly degree)
    (symmetric : SymmetricSolution polynomial) :
    (bind₁ ![X 2, -X 0, X 0] polynomial.val : Poly) = 0 := by
  apply MvPolynomial.funext
  intro values
  rw [eval_bind, map_zero]
  have coordinates : (fun index => eval values (![X 2, -X 0, X 0] index)) =
      ![values 2, -values 0, values 0] := by
    ext index
    fin_cases index <;> simp
  rw [coordinates, symmetric_eval_swap_last polynomial symmetric (values 2) (values 0) (-values 0),
    ← symmetric_eval_cyclic polynomial symmetric (values 2) (values 0) (-values 0)]
  exact symmetric_opposite_vanishes polynomial symmetric (values 0) (values 2)

theorem bernoulliOperator_bind_zero (degree : ℕ) (substitution : Fin 3 → Poly)
    (parameter polynomial : Poly) (parameter_zero : bind₁ substitution parameter = 0) :
    bind₁ substitution (bernoulliOperator degree parameter polynomial) =
      bind₁ substitution polynomial := by
  classical
  unfold bernoulliOperator
  rw [map_sum]
  rw [Finset.sum_eq_single 0]
  · simp [bernoulli_zero]
  · intro index _ index_ne
    simp only [map_mul, map_pow, map_neg, parameter_zero, neg_zero,
      zero_pow index_ne, mul_zero, zero_mul]
  · simp

theorem bernoulliObstruction_zero_second_variable {degree : ℕ}
    (polynomial : HomogeneousPoly degree) (symmetric : SymmetricSolution polynomial) :
    (bind₁ ![X 0, 0, X 2] (bernoulliObstruction polynomial) : Poly) = 0 := by
  let substitution : Fin 3 → Poly := ![X 0, 0, X 2]
  have second_variable_zero : bind₁ substitution (X 1) = 0 := by
    simp [substitution]
  have first_frame :
      bind₁ substitution (bind₁ ![X 2 - 2 * X 1, -X 0, X 0 - X 1] polynomial.val) =
        bind₁ ![X 2, -X 0, X 0] polynomial.val := by
    rw [bind₁_bind₁]
    congr 1
    ext index
    fin_cases index <;> simp [substitution]
  change bind₁ substitution (bernoulliObstruction polynomial) = 0
  simp only [bernoulliObstruction, map_sub, map_mul, second_variable_zero,
    zero_mul, sub_zero]
  rw [bernoulliOperator_bind_zero degree substitution (X 1) _ second_variable_zero,
    first_frame, symmetric_opposite_substitution polynomial symmetric, mul_zero]

end TernaryPeriodPolynomials.PolynomialBernoulliDetection.Helpers
