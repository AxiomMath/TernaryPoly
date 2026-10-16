module

public import TernaryPeriodPolynomials.Building.BoundaryApartments.Good.Apartments
public import Mathlib.Tactic.LinearCombination

@[expose] public section


open GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers

open Matrix Homogeneous MvPolynomial

def polynomialValue (polynomial : Poly) (first second third : ℂ) : ℂ :=
  eval ![first, second, third] polynomial

theorem polynomialValue_bind (polynomial : Poly) (substitution : Fin 3 → Poly)
    (first second third : ℂ) :
    polynomialValue (bind₁ substitution polynomial) first second third =
      eval (fun index => polynomialValue (substitution index) first second third) polynomial := by
  have hom_equality : (eval ![first, second, third]).comp (bind₁ substitution).toRingHom =
      eval (fun index => polynomialValue (substitution index) first second third) := by
    apply MvPolynomial.ringHom_ext
    · intro coefficient
      simp
    · intro index
      simp [polynomialValue]
  exact RingHom.congr_fun hom_equality polynomial

theorem polynomialValue_permute {degree : ℕ} {polynomial : HomogeneousPoly degree}
    (solution : SymmetricSolution polynomial) (permutation : Equiv.Perm (Fin 3))
    (first second third : ℂ) :
    eval (fun index => ![first, second, third] (permutation index)) polynomial.val =
      polynomialValue polynomial.val first second third := by
  have evaluated := congrArg (eval ![first, second, third]) (solution.1 permutation)
  change polynomialValue (bind₁ (fun index => X (permutation index)) polynomial.val)
    first second third = polynomialValue polynomial.val first second third at evaluated
  rw [polynomialValue_bind] at evaluated
  simpa only [polynomialValue, eval_X] using evaluated

theorem polynomialValue_swap_first {degree : ℕ} {polynomial : HomogeneousPoly degree}
    (solution : SymmetricSolution polynomial) (first second third : ℂ) :
    polynomialValue polynomial.val second first third =
      polynomialValue polynomial.val first second third := by
  have value := polynomialValue_permute solution (Equiv.swap 0 1) first second third
  have coordinate : (fun index => ![first, second, third] ((Equiv.swap (0 : Fin 3) 1) index)) =
      ![second, first, third] := by
    funext index
    fin_cases index <;> norm_num [Equiv.swap_apply_def]
  simpa only [coordinate, polynomialValue] using value

theorem polynomialValue_swap_last {degree : ℕ} {polynomial : HomogeneousPoly degree}
    (solution : SymmetricSolution polynomial) (first second third : ℂ) :
    polynomialValue polynomial.val first third second =
      polynomialValue polynomial.val first second third := by
  have value := polynomialValue_permute solution (Equiv.swap 1 2) first second third
  have coordinate : (fun index => ![first, second, third] ((Equiv.swap (1 : Fin 3) 2) index)) =
      ![first, third, second] := by
    funext index
    fin_cases index <;> simp [Equiv.swap_apply_def, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
  simpa only [coordinate, polynomialValue] using value

theorem polynomialValue_cyclic {degree : ℕ} {polynomial : HomogeneousPoly degree}
    (solution : SymmetricSolution polynomial) (first second third : ℂ) :
    polynomialValue polynomial.val third first second =
      polynomialValue polynomial.val first second third := by
  rw [polynomialValue_swap_first solution, polynomialValue_swap_last solution]

theorem polynomialValue_norm_first {degree : ℕ} {polynomial : HomogeneousPoly degree}
    (solution : SymmetricSolution polynomial) (first second third : ℂ) :
    polynomialValue polynomial.val first second third +
      polynomialValue polynomial.val (-second) (first - second) third +
      polynomialValue polynomial.val (second - first) (-first) third = 0 := by
  have value := congrArg (eval ![first, second, third]) solution.2
  simp only [map_add, map_zero] at value
  change polynomialValue polynomial.val first second third +
    polynomialValue (bind₁ ![-X 1, X 0 - X 1, X 2] polynomial.val) first second third +
    polynomialValue (bind₁ ![X 1 - X 0, -X 0, X 2] polynomial.val) first second third = 0 at value
  rw [polynomialValue_bind, polynomialValue_bind] at value
  have first_coordinate : (fun index => polynomialValue (![-X 1, X 0 - X 1, X 2] index)
      first second third) = ![-second, first - second, third] := by
    funext index
    fin_cases index <;> simp [polynomialValue]
  have second_coordinate : (fun index => polynomialValue (![X 1 - X 0, -X 0, X 2] index)
      first second third) = ![second - first, -first, third] := by
    funext index
    fin_cases index <;> simp [polynomialValue]
  rw [first_coordinate, second_coordinate] at value
  exact value

theorem polynomialValue_norm_last {degree : ℕ} {polynomial : HomogeneousPoly degree}
    (solution : SymmetricSolution polynomial) (first second third : ℂ) :
    polynomialValue polynomial.val first second third +
      polynomialValue polynomial.val first (-third) (second - third) +
      polynomialValue polynomial.val first (third - second) (-second) = 0 := by
  have value := polynomialValue_norm_first solution second third first
  simpa only [← polynomialValue_cyclic solution] using value

theorem homogeneousValue_scale {degree : ℕ} (polynomial : HomogeneousPoly degree)
    (scalar : ℂ) (coordinates : Fin 3 → ℂ) :
    eval (fun index => scalar * coordinates index) polynomial.val =
      scalar ^ degree * eval coordinates polynomial.val := by
  classical
  simp only [eval_eq, Finset.mul_sum, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum]
  apply Finset.sum_congr rfl
  intro monomial monomial_support
  have monomial_degree : ∑ index ∈ monomial.support, monomial index = degree := by
    simpa only [Finsupp.weight_apply, Finsupp.sum, Pi.one_apply, smul_eq_mul, mul_one] using
      polynomial.property (Finsupp.mem_support_iff.mp monomial_support)
  rw [monomial_degree]
  ring

theorem polynomialValue_neg {degree : ℕ} (polynomial : HomogeneousPoly degree)
    (first second third : ℂ) :
    polynomialValue polynomial.val (-first) (-second) (-third) =
      (-1 : ℂ) ^ degree * polynomialValue polynomial.val first second third := by
  have value := homogeneousValue_scale polynomial (-1) ![first, second, third]
  have coordinate : (fun index => (-1 : ℂ) * ![first, second, third] index) =
      ![-first, -second, -third] := by
    funext index
    fin_cases index <;> simp
  simpa only [coordinate, polynomialValue] using value

theorem polynomialValue_opposite_translation {degree : ℕ}
    {polynomial : HomogeneousPoly degree} (solution : SymmetricSolution polynomial)
    (first second : ℂ) :
    polynomialValue polynomial.val first (-first) second =
      polynomialValue polynomial.val (first + second) (-(first + second)) second := by
  let sign : ℂ := (-1) ^ degree
  have sign_square : sign * sign = 1 := by
    dsimp [sign]
    rw [← mul_pow]
    norm_num
  have first_norm := polynomialValue_norm_last solution (-first) (-second) first
  have second_norm := polynomialValue_norm_last solution (-(first + second)) (-second) first
  have third_norm := polynomialValue_norm_last solution (-(first + second)) (-first) (-first)
  have fourth_norm := polynomialValue_norm_first solution (-(first + second)) 0 first
  have negative_sum : -second - first = -(first + second) := by ring
  simp only [negative_sum, sub_neg_eq_add, neg_neg, sub_self, sub_zero, neg_zero, zero_add]
    at first_norm second_norm third_norm fourth_norm
  have first_term : polynomialValue polynomial.val (-first) (-second) first =
      sign * polynomialValue polynomial.val first (-first) second := by
    have value := polynomialValue_neg polynomial first second (-first)
    simpa only [neg_neg, polynomialValue_swap_last solution] using value
  have second_term := polynomialValue_neg polynomial first first (first + second)
  have third_term : polynomialValue polynomial.val (-(first + second)) (-second) first =
      sign * polynomialValue polynomial.val (-first) (first + second) second := by
    have value := polynomialValue_neg polynomial (first + second) second (-first)
    simpa only [neg_neg, polynomialValue_cyclic solution] using value
  have fourth_term : polynomialValue polynomial.val (-(first + second)) (-first) (-(first + second)) =
      sign * polynomialValue polynomial.val (first + second) (first + second) first := by
    have value := polynomialValue_neg polynomial (first + second) first (first + second)
    simpa only [polynomialValue_swap_last solution] using value
  have fifth_term : polynomialValue polynomial.val (-(first + second)) (-first) (-first) =
      sign * polynomialValue polynomial.val first first (first + second) := by
    have value := polynomialValue_neg polynomial (first + second) first first
    simpa only [← polynomialValue_cyclic solution] using value
  rw [first_term, second_term] at first_norm
  rw [third_term, fourth_term] at second_norm
  have opposite_swap : polynomialValue polynomial.val (-(first + second)) (first + second) second =
      polynomialValue polynomial.val (first + second) (-(first + second)) second :=
    polynomialValue_swap_first solution _ _ _
  rw [opposite_swap] at second_norm
  rw [fifth_term] at third_norm
  have zero_first : polynomialValue polynomial.val 0 (-(first + second)) first =
      polynomialValue polynomial.val (-(first + second)) first 0 := by
    rw [polynomialValue_swap_first solution, polynomialValue_swap_last solution]
  rw [zero_first] at fourth_norm
  have translated : sign * (polynomialValue polynomial.val first (-first) second -
      polynomialValue polynomial.val (first + second) (-(first + second)) second) = 0 := by
    linear_combination first_norm - sign * second_norm - third_norm + fourth_norm +
      (polynomialValue polynomial.val (-first) (first + second) second +
        polynomialValue polynomial.val (first + second) (first + second) first) * sign_square
  have sign_nonzero : sign ≠ 0 := by
    intro sign_zero
    simp [sign_zero] at sign_square
  exact sub_eq_zero.mp ((mul_eq_zero.mp translated).resolve_left sign_nonzero)

def oppositePolynomial (polynomial : Poly) (parameter : ℂ) : Polynomial ℂ :=
  eval₂Hom Polynomial.C ![Polynomial.X, -Polynomial.X, Polynomial.C parameter] polynomial

theorem oppositePolynomial_eval (polynomial : Poly) (parameter point : ℂ) :
    Polynomial.eval point (oppositePolynomial polynomial parameter) =
      polynomialValue polynomial point (-point) parameter := by
  unfold oppositePolynomial
  change (Polynomial.evalRingHom point) ((eval₂Hom Polynomial.C
    ![Polynomial.X, -Polynomial.X, Polynomial.C parameter]) polynomial) = _
  rw [MvPolynomial.map_eval₂Hom]
  have coefficients : (Polynomial.evalRingHom point).comp Polynomial.C = RingHom.id ℂ := by
    ext coefficient
    simp
  have coordinates : (fun index => (Polynomial.evalRingHom point)
      (![Polynomial.X, -Polynomial.X, Polynomial.C parameter] index)) =
      ![point, -point, parameter] := by
    funext index
    fin_cases index <;> simp
  rw [coefficients, coordinates]
  rfl

theorem polynomialValue_opposite_zero {degree : ℕ} {polynomial : HomogeneousPoly degree}
    (solution : SymmetricSolution polynomial) (first second : ℂ) :
    polynomialValue polynomial.val first (-first) second = 0 := by
  have origin_value : polynomialValue polynomial.val 0 0 second = 0 := by
    have norm := polynomialValue_norm_first solution 0 0 second
    simp only [neg_zero, sub_self] at norm
    linear_combination (1 / 3 : ℂ) * norm
  by_cases second_zero : second = 0
  · subst second
    let parameterPolynomial : Polynomial ℂ :=
      eval₂Hom Polynomial.C ![Polynomial.C first, Polynomial.C (-first), Polynomial.X] polynomial.val
    have parameter_eval (parameter : ℂ) : Polynomial.eval parameter parameterPolynomial =
        polynomialValue polynomial.val first (-first) parameter := by
      change (Polynomial.evalRingHom parameter) ((eval₂Hom Polynomial.C
        ![Polynomial.C first, Polynomial.C (-first), Polynomial.X]) polynomial.val) = _
      rw [MvPolynomial.map_eval₂Hom]
      have coefficients : (Polynomial.evalRingHom parameter).comp Polynomial.C = RingHom.id ℂ := by
        ext coefficient
        simp
      have coordinates : (fun index => (Polynomial.evalRingHom parameter)
          (![Polynomial.C first, Polynomial.C (-first), Polynomial.X] index)) =
          ![first, -first, parameter] := by
        funext index
        fin_cases index <;> simp
      rw [coefficients, coordinates]
      rfl
    have vanishes_nonzero (parameter : ℂ) (parameter_nonzero : parameter ≠ 0) :
        Polynomial.eval parameter parameterPolynomial = 0 := by
      rw [parameter_eval]
      let restriction := oppositePolynomial polynomial.val parameter
      have points (iterations : ℕ) : Polynomial.eval ((iterations : ℂ) * parameter) restriction = 0 := by
        induction iterations with
        | zero => simpa [restriction, oppositePolynomial_eval] using
            (show polynomialValue polynomial.val 0 0 parameter = 0 from by
              have norm := polynomialValue_norm_first solution 0 0 parameter
              simp only [neg_zero, sub_self] at norm
              linear_combination (1 / 3 : ℂ) * norm)
        | succ iterations induction_hypothesis =>
          rw [show ((iterations + 1 : ℕ) : ℂ) * parameter = (iterations : ℂ) * parameter + parameter by
            push_cast; ring, oppositePolynomial_eval]
          rw [← polynomialValue_opposite_translation solution]
          simpa only [restriction, oppositePolynomial_eval] using induction_hypothesis
      have points_injective : Function.Injective (fun iterations : ℕ => (iterations : ℂ) * parameter) := by
        intro left right equality
        exact Nat.cast_injective ((mul_right_cancel₀ parameter_nonzero) equality)
      have zero_restriction : restriction = 0 := by
        apply Polynomial.eq_of_infinite_eval_eq restriction 0
        apply (Set.infinite_range_of_injective points_injective).mono
        rintro point ⟨iterations, rfl⟩
        simpa using points iterations
      have value := congrArg (Polynomial.eval first) zero_restriction
      simpa only [restriction, oppositePolynomial_eval, Polynomial.eval_zero] using value
    have zero_parameterPolynomial : parameterPolynomial = 0 := by
      apply Polynomial.eq_of_infinite_eval_eq parameterPolynomial 0
      apply (Set.infinite_univ.sdiff (Set.finite_singleton (0 : ℂ))).mono
      intro parameter parameter_in_set
      simp only [Set.mem_sdiff, Set.mem_univ, Set.mem_singleton_iff, true_and] at parameter_in_set
      simpa using vanishes_nonzero parameter parameter_in_set
    have value := congrArg (Polynomial.eval 0) zero_parameterPolynomial
    simpa only [parameter_eval, Polynomial.eval_zero] using value
  · let restriction := oppositePolynomial polynomial.val second
    have points (iterations : ℕ) : Polynomial.eval ((iterations : ℂ) * second) restriction = 0 := by
      induction iterations with
      | zero => simpa [restriction, oppositePolynomial_eval] using origin_value
      | succ iterations induction_hypothesis =>
        rw [show ((iterations + 1 : ℕ) : ℂ) * second = (iterations : ℂ) * second + second by
          push_cast; ring, oppositePolynomial_eval]
        rw [← polynomialValue_opposite_translation solution]
        simpa only [restriction, oppositePolynomial_eval] using induction_hypothesis
    have points_injective : Function.Injective (fun iterations : ℕ => (iterations : ℂ) * second) := by
      intro left right equality
      exact Nat.cast_injective ((mul_right_cancel₀ second_zero) equality)
    have zero_restriction : restriction = 0 := by
      apply Polynomial.eq_of_infinite_eval_eq restriction 0
      apply (Set.infinite_range_of_injective points_injective).mono
      rintro point ⟨iterations, rfl⟩
      simpa using points iterations
    have value := congrArg (Polynomial.eval first) zero_restriction
    simpa only [restriction, oppositePolynomial_eval, Polynomial.eval_zero] using value

end TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers
