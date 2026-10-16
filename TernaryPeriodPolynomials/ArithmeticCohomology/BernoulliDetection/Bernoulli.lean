module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BernoulliDetection.Polynomial
public import Mathlib.NumberTheory.BernoulliPolynomials
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.MvPolynomial.Equiv

@[expose] public section


open GeneralEisenstein MvPolynomial

namespace TernaryPeriodPolynomials.PolynomialBernoulliDetection.Helpers

theorem finSuccEquiv_pderiv (polynomial : Poly) :
    finSuccEquiv ℂ 2 (pderiv 0 polynomial) =
      Polynomial.derivative (finSuccEquiv ℂ 2 polynomial) := by
  induction polynomial using MvPolynomial.induction_on with
  | C coefficient => simp [finSuccEquiv_apply]
  | add left right left_eq right_eq =>
    simp only [map_add, left_eq, right_eq]
  | mul_X polynomial index induction_hypothesis =>
    fin_cases index
    · change finSuccEquiv ℂ 2 (pderiv 0 (polynomial * X 0)) =
        Polynomial.derivative (finSuccEquiv ℂ 2 (polynomial * X 0))
      simp only [Derivation.leibniz, smul_eq_mul, pderiv_X_self,
        map_add, map_mul, mul_one, finSuccEquiv_X_zero,
        Polynomial.derivative_mul, Polynomial.derivative_X, induction_hypothesis]
      ring
    · have coordinate : finSuccEquiv ℂ 2 (X (1 : Fin 3)) = Polynomial.C (X (0 : Fin 2)) :=
        finSuccEquiv_X_succ (j := 0)
      simp [Derivation.leibniz, coordinate, induction_hypothesis, mul_comm]
    · have coordinate : finSuccEquiv ℂ 2 (X (2 : Fin 3)) = Polynomial.C (X (1 : Fin 2)) :=
        finSuccEquiv_X_succ (j := 1)
      simp [Derivation.leibniz, coordinate, induction_hypothesis, mul_comm]

theorem finSuccEquiv_iterate_pderiv (iterations : ℕ) (polynomial : Poly) :
    finSuccEquiv ℂ 2 (((fun polynomial : Poly => pderiv 0 polynomial)^[iterations]) polynomial) =
      (Polynomial.derivative^[iterations]) (finSuccEquiv ℂ 2 polynomial) := by
  induction iterations with
  | zero => rfl
  | succ iterations induction_hypothesis =>
    simp only [Function.iterate_succ_apply', finSuccEquiv_pderiv, induction_hypothesis]

theorem iterate_pderiv_eq_zero {degree : ℕ} (polynomial : HomogeneousPoly degree)
    {iterations : ℕ} (greater : degree < iterations) :
    ((fun polynomial : Poly => pderiv 0 polynomial)^[iterations]) polynomial.val = 0 := by
  apply (finSuccEquiv ℂ 2).injective
  rw [finSuccEquiv_iterate_pderiv, map_zero]
  apply Polynomial.iterate_derivative_eq_zero
  rw [natDegree_finSuccEquiv]
  apply lt_of_le_of_lt (degreeOf_le_totalDegree polynomial.val 0)
  by_cases nonzero : polynomial.val = 0
  · simp [nonzero]
    exact lt_of_le_of_lt (Nat.zero_le degree) greater
  · rw [polynomial.property.totalDegree nonzero]
    exact greater

theorem bernoulli_sum_translation (degree : ℕ) (point : ℂ) :
    (∑ index ∈ Finset.range (degree + 1),
      (bernoulli index : ℂ) * (degree.choose index : ℂ) * (point + 1) ^ (degree - index)) -
      (∑ index ∈ Finset.range (degree + 1),
        (bernoulli index : ℂ) * (degree.choose index : ℂ) * point ^ (degree - index)) =
      (degree : ℂ) * point ^ (degree - 1) := by
  have equality := congrArg (fun polynomial : Polynomial ℚ =>
    Polynomial.eval point (polynomial.map (algebraMap ℚ ℂ)))
    (Polynomial.bernoulli_comp_one_add_X degree)
  simp only [nsmul_eq_mul] at equality
  simp only [Polynomial.map_comp, Polynomial.map_add, Polynomial.map_one,
    Polynomial.map_X, Polynomial.map_mul, Polynomial.map_natCast, Polynomial.map_pow,
    Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_X,
    Polynomial.eval_mul, Polynomial.eval_natCast, Polynomial.eval_pow] at equality
  have expansion (point : ℂ) :
      Polynomial.eval point ((Polynomial.bernoulli degree).map (algebraMap ℚ ℂ)) =
        ∑ index ∈ Finset.range (degree + 1),
          (bernoulli index : ℂ) * (degree.choose index : ℂ) * point ^ (degree - index) := by
    rw [Polynomial.bernoulli_def, Polynomial.map_sum, Polynomial.eval_finsetSum]
    rw [← Finset.sum_range_reflect]
    apply Finset.sum_congr rfl
    intro index membership
    have bound : index ≤ degree := Nat.le_of_lt_succ (Finset.mem_range.mp membership)
    simp only [Nat.add_sub_cancel, Nat.sub_sub_self bound, Polynomial.map_monomial,
      Polynomial.eval_monomial, map_mul, map_natCast, Nat.choose_symm bound]
    rfl
  rw [expansion, expansion] at equality
  rw [add_comm (∑ index ∈ Finset.range (degree + 1),
    (bernoulli index : ℂ) * (degree.choose index : ℂ) * point ^ (degree - index))] at equality
  simpa only [add_comm point 1] using sub_eq_iff_eq_add.mpr equality

noncomputable def complexBernoulliOperator (degree : ℕ) (parameter : ℂ) (polynomial : Polynomial ℂ) :
    Polynomial ℂ :=
  ∑ index ∈ Finset.range (degree + 1),
    Polynomial.C ((bernoulli index : ℂ) / (index.factorial : ℂ) * (-parameter) ^ index) *
      (Polynomial.derivative^[index]) polynomial

theorem complexBernoulliOperator_add (degree : ℕ) (parameter : ℂ)
    (left right : Polynomial ℂ) :
    complexBernoulliOperator degree parameter (left + right) =
      complexBernoulliOperator degree parameter left +
        complexBernoulliOperator degree parameter right := by
  have iterates (index : ℕ) :
      (Polynomial.derivative^[index]) (left + right) =
        (Polynomial.derivative^[index]) left + (Polynomial.derivative^[index]) right := by
    induction index with
    | zero => rfl
    | succ index induction_hypothesis =>
      simp only [Function.iterate_succ_apply', induction_hypothesis, map_add]
  simp [complexBernoulliOperator, iterates, mul_add,
    Finset.sum_add_distrib]

theorem complexBernoulliOperator_sub (degree : ℕ) (parameter : ℂ)
    (left right : Polynomial ℂ) :
    complexBernoulliOperator degree parameter (left - right) =
      complexBernoulliOperator degree parameter left -
        complexBernoulliOperator degree parameter right := by
  simp [complexBernoulliOperator, mul_sub,
    Finset.sum_sub_distrib]

theorem complexBernoulliOperator_C_mul (degree : ℕ) (parameter coefficient : ℂ)
    (polynomial : Polynomial ℂ) :
    complexBernoulliOperator degree parameter (Polynomial.C coefficient * polynomial) =
      Polynomial.C coefficient * complexBernoulliOperator degree parameter polynomial := by
  simp only [complexBernoulliOperator, Polynomial.iterate_derivative_C_mul,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro index _
  ring

theorem complexBernoulliOperator_X_pow_eval (degree power : ℕ) (parameter point : ℂ)
    (bound : power ≤ degree) :
    (complexBernoulliOperator degree parameter (Polynomial.X ^ power)).eval point =
      ∑ index ∈ Finset.range (power + 1),
        (bernoulli index : ℂ) * (power.choose index : ℂ) *
          (-parameter) ^ index * point ^ (power - index) := by
  simp only [complexBernoulliOperator, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.iterate_derivative_X_pow_eq_natCast_mul,
    Polynomial.eval_natCast, Polynomial.eval_pow, Polynomial.eval_X]
  rw [← Finset.sum_subset (Finset.range_mono (Nat.add_le_add_right bound 1))]
  · apply Finset.sum_congr rfl
    intro index _
    rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
    have factorial_ne : (index.factorial : ℂ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero index
    field_simp
  · intro index membership outside
    have greater : power < index := by
      have lower := not_lt.mp (fun less => outside (Finset.mem_range.mpr less))
      omega
    simp [Nat.descFactorial_of_lt greater]

theorem complexBernoulliOperator_X_pow_translation (degree power : ℕ)
    (parameter point : ℂ) (bound : power ≤ degree) :
    (complexBernoulliOperator degree parameter (Polynomial.X ^ power)).eval (point - parameter) -
      (complexBernoulliOperator degree parameter (Polynomial.X ^ power)).eval point =
        -parameter * (power : ℂ) * point ^ (power - 1) := by
  by_cases parameter_zero : parameter = 0
  · simp [parameter_zero]
  · let scaledPoint := point / (-parameter)
    have scaled_eq : point = -parameter * scaledPoint := by
      dsimp [scaledPoint]
      field_simp
    have shifted_eq : point - parameter = -parameter * (scaledPoint + 1) := by
      rw [scaled_eq]
      ring
    rw [complexBernoulliOperator_X_pow_eval degree power parameter (point - parameter) bound,
      complexBernoulliOperator_X_pow_eval degree power parameter point bound,
      shifted_eq, scaled_eq]
    have scaled_sum (value : ℂ) :
        (∑ index ∈ Finset.range (power + 1),
          (bernoulli index : ℂ) * (power.choose index : ℂ) * (-parameter) ^ index *
            (-parameter * value) ^ (power - index)) =
          (-parameter) ^ power * ∑ index ∈ Finset.range (power + 1),
            (bernoulli index : ℂ) * (power.choose index : ℂ) * value ^ (power - index) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro index membership
      have index_bound : index ≤ power := Nat.le_of_lt_succ (Finset.mem_range.mp membership)
      rw [mul_pow]
      calc
        _ = ((-parameter) ^ index * (-parameter) ^ (power - index)) *
            ((bernoulli index : ℂ) * (power.choose index : ℂ) * value ^ (power - index)) := by ring
        _ = _ := by rw [← pow_add, Nat.add_sub_of_le index_bound]
    rw [scaled_sum, scaled_sum, ← mul_sub, bernoulli_sum_translation]
    by_cases positive : power = 0
    · simp [positive]
    · have power_eq : power = 1 + (power - 1) := by omega
      rw [power_eq, pow_add, Nat.add_sub_cancel_left]
      simp only [pow_one, mul_pow]
      ring

theorem complexBernoulliOperator_translation (degree : ℕ) (parameter : ℂ)
    (polynomial : Polynomial ℂ) (bound : polynomial.natDegree ≤ degree) :
    complexBernoulliOperator degree parameter
      ((Polynomial.taylor (-parameter)) polynomial - polynomial) =
        Polynomial.C (-parameter) * Polynomial.derivative polynomial := by
  have summation : polynomial =
      ∑ power ∈ Finset.range (degree + 1),
        Polynomial.C (polynomial.coeff power) * Polynomial.X ^ power := by
    simpa only [Polynomial.C_mul_X_pow_eq_monomial] using
      Polynomial.as_sum_range' polynomial (degree + 1) (Nat.lt_succ_of_le bound)
  rw [summation]
  simp only [map_sum, ← Finset.sum_sub_distrib,
    Finset.mul_sum]
  have operator_sum (indexSet : Finset ℕ) (terms : ℕ → Polynomial ℂ) :
      complexBernoulliOperator degree parameter (∑ index ∈ indexSet, terms index) =
        ∑ index ∈ indexSet, complexBernoulliOperator degree parameter (terms index) := by
    simp only [complexBernoulliOperator, Polynomial.iterate_derivative_sum, Finset.mul_sum]
    exact Finset.sum_comm
  rw [operator_sum]
  apply Finset.sum_congr rfl
  intro power membership
  have power_bound : power ≤ degree := Nat.le_of_lt_succ (Finset.mem_range.mp membership)
  simp only [Polynomial.taylor_mul, Polynomial.taylor_C, Polynomial.taylor_X_pow,
    ← mul_sub, complexBernoulliOperator_C_mul, Polynomial.derivative_C_mul]
  rw [mul_left_comm]
  congr 1
  apply Polynomial.funext
  intro point
  rw [complexBernoulliOperator_sub]
  have translated_operator :
      (complexBernoulliOperator degree parameter ((Polynomial.X + Polynomial.C (-parameter)) ^ power)).eval point =
        (complexBernoulliOperator degree parameter (Polynomial.X ^ power)).eval (point - parameter) := by
    simp only [complexBernoulliOperator, Polynomial.eval_finsetSum, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.iterate_derivative_X_add_pow,
      Polynomial.iterate_derivative_X_pow_eq_natCast_mul, nsmul_eq_mul,
      Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X,
      Polynomial.eval_natCast]
    simp only [sub_eq_add_neg]
  rw [Polynomial.eval_sub, translated_operator,
    complexBernoulliOperator_X_pow_translation degree power parameter point power_bound]
  simp [Polynomial.derivative_X_pow, mul_assoc]

theorem finSuccEquiv_specialize_pderiv (second third : ℂ) (polynomial : Poly) :
    (finSuccEquiv ℂ 2 (pderiv 0 polynomial)).map (eval ![second, third]) =
      Polynomial.derivative ((finSuccEquiv ℂ 2 polynomial).map (eval ![second, third])) := by
  rw [finSuccEquiv_pderiv, Polynomial.derivative_map]

theorem eval_bernoulliOperator (degree : ℕ) (parameter polynomial : Poly)
    (point second third : ℂ) :
    eval ![point, second, third] (bernoulliOperator degree parameter polynomial) =
      (complexBernoulliOperator degree (eval ![point, second, third] parameter)
        ((finSuccEquiv ℂ 2 polynomial).map (eval ![second, third]))).eval point := by
  simp only [bernoulliOperator, complexBernoulliOperator, map_sum, map_mul,
    map_pow, map_neg, eval_C, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_neg]
  apply Finset.sum_congr rfl
  intro index _
  congr 1
  rw [Polynomial.iterate_derivative_map, ← finSuccEquiv_iterate_pderiv]
  have coordinates : Fin.cons point ![second, third] = ![point, second, third] := by
    ext coordinate
    fin_cases coordinate <;> rfl
  simpa only [coordinates] using
    (eval_eq_eval_mv_eval' ![second, third] point
      (((fun polynomial : Poly => pderiv 0 polynomial)^[index]) polynomial))

theorem mapped_bernoulli_natDegree (degree : ℕ) :
    ((Polynomial.bernoulli degree).map (algebraMap ℚ ℂ)).natDegree ≤ degree := by
  rw [Polynomial.bernoulli_def, Polynomial.map_sum]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro index membership
  rw [Polynomial.map_monomial]
  exact (Polynomial.natDegree_monomial_le _).trans
    (Nat.le_of_lt_succ (Finset.mem_range.mp membership))

theorem polynomial_antidifference (degree : ℕ) (parameter : ℂ)
    (parameter_ne : parameter ≠ 0) (polynomial : Polynomial ℂ)
    (bound : polynomial.natDegree ≤ degree) :
    ∃ antiderivative : Polynomial ℂ,
      antiderivative.natDegree ≤ degree + 1 ∧
        Polynomial.taylor (-parameter) antiderivative - antiderivative = polynomial := by
  let basic (power : ℕ) : Polynomial ℂ :=
    Polynomial.C ((-parameter) ^ power / (power + 1 : ℂ)) *
      ((Polynomial.bernoulli (power + 1)).map (algebraMap ℚ ℂ)).comp
        (Polynomial.C (-parameter)⁻¹ * Polynomial.X)
  have basic_bound (power : ℕ) : (basic power).natDegree ≤ power + 1 := by
    apply (Polynomial.natDegree_C_mul_le _ _).trans
    apply (Polynomial.natDegree_comp_le).trans
    have scale_bound : (Polynomial.C (-parameter)⁻¹ * Polynomial.X).natDegree ≤ 1 := by
      exact (Polynomial.natDegree_C_mul_le _ _).trans (by simp)
    exact (Nat.mul_le_mul (mapped_bernoulli_natDegree (power + 1)) scale_bound).trans (by simp)
  have basic_difference (power : ℕ) :
      Polynomial.taylor (-parameter) (basic power) - basic power = Polynomial.X ^ power := by
    apply Polynomial.funext
    intro point
    have evaluation (argument : ℂ) : (basic power).eval argument =
        ((-parameter) ^ power / (power + 1 : ℂ)) *
          Polynomial.eval ((-parameter)⁻¹ * argument)
            ((Polynomial.bernoulli (power + 1)).map (algebraMap ℚ ℂ)) := by
      simp [basic]
    rw [Polynomial.eval_sub, Polynomial.taylor_eval, evaluation, evaluation]
    rw [← mul_sub]
    have shift : (-parameter)⁻¹ * (point + -parameter) =
        1 + (-parameter)⁻¹ * point := by
      field_simp
      ring
    rw [shift]
    have equality := congrArg (fun polynomial : Polynomial ℚ =>
      Polynomial.eval ((-parameter)⁻¹ * point) (polynomial.map (algebraMap ℚ ℂ)))
      (Polynomial.bernoulli_comp_one_add_X (power + 1))
    simp only [nsmul_eq_mul] at equality
    simp only [Polynomial.map_comp, Polynomial.map_add, Polynomial.map_one,
      Polynomial.map_X, Polynomial.map_mul, Polynomial.map_natCast, Polynomial.map_pow,
      Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_X,
      Polynomial.eval_mul, Polynomial.eval_natCast, Polynomial.eval_pow,
      Nat.add_sub_cancel] at equality
    rw [equality, add_sub_cancel_left]
    simp only [Polynomial.eval_pow, Polynomial.eval_X, mul_pow, inv_pow]
    have successor_ne : (power + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero power
    have negative_ne : -parameter ≠ 0 := neg_ne_zero.mpr parameter_ne
    field_simp
    simp only [Nat.cast_add, Nat.cast_one]
  let antiderivative : Polynomial ℂ :=
    ∑ power ∈ Finset.range (degree + 1), Polynomial.C (polynomial.coeff power) * basic power
  refine ⟨antiderivative, ?_, ?_⟩
  · apply Polynomial.natDegree_sum_le_of_forall_le
    intro power membership
    exact (Polynomial.natDegree_C_mul_le _ _).trans
      ((basic_bound power).trans (Nat.add_le_add_right
        (Nat.le_of_lt_succ (Finset.mem_range.mp membership)) 1))
  · simp only [antiderivative, map_sum, Polynomial.taylor_mul, Polynomial.taylor_C,
      ← Finset.sum_sub_distrib, ← mul_sub, basic_difference,
      Polynomial.C_mul_X_pow_eq_monomial]
    exact (Polynomial.as_sum_range' polynomial (degree + 1) (Nat.lt_succ_of_le bound)).symm

theorem complexBernoulliOperator_degree_extend {degree larger : ℕ} (parameter : ℂ)
    (polynomial : Polynomial ℂ) (bound : polynomial.natDegree ≤ degree)
    (degree_bound : degree ≤ larger) :
    complexBernoulliOperator larger parameter polynomial =
      complexBernoulliOperator degree parameter polynomial := by
  unfold complexBernoulliOperator
  symm
  apply Finset.sum_subset (Finset.range_mono (Nat.add_le_add_right degree_bound 1))
  intro index _ outside
  have greater : degree < index := by
    have lower := not_lt.mp (fun less => outside (Finset.mem_range.mpr less))
    omega
  rw [Polynomial.iterate_derivative_eq_zero (lt_of_le_of_lt bound greater), mul_zero]

theorem complexBernoulliOperator_C (degree : ℕ) (parameter coefficient : ℂ) :
    complexBernoulliOperator degree parameter (Polynomial.C coefficient) =
      Polynomial.C coefficient := by
  have equality := complexBernoulliOperator_degree_extend parameter (Polynomial.C coefficient)
    (by simp : (Polynomial.C coefficient).natDegree ≤ 0) (Nat.zero_le degree)
  rw [equality]
  simp [complexBernoulliOperator, bernoulli_zero]

theorem polynomial_radical_coordinate_constant (degree : ℕ) (first second : ℂ)
    (first_ne : first ≠ 0) (left right : Polynomial ℂ)
    (left_bound : left.natDegree ≤ degree) (right_bound : right.natDegree ≤ degree)
    (cocycle : Polynomial.taylor (-first) right - right =
      Polynomial.taylor (-second) left - left) :
    ∃ coefficient : ℂ,
      Polynomial.C second * complexBernoulliOperator degree first left -
        Polynomial.C first * complexBernoulliOperator degree second right =
          Polynomial.C coefficient := by
  obtain ⟨antiderivative, antiderivative_bound, difference⟩ :=
    polynomial_antidifference degree first first_ne left left_bound
  let remainder := right - (Polynomial.taylor (-second) antiderivative - antiderivative)
  have periodic : Polynomial.taylor (-first) remainder = remainder := by
    have commuting := Polynomial.taylor_taylor antiderivative (-second) (-first)
    have commuting' := Polynomial.taylor_taylor antiderivative (-first) (-second)
    have equality : Polynomial.taylor (-first) (Polynomial.taylor (-second) antiderivative) =
        Polynomial.taylor (-second) (Polynomial.taylor (-first) antiderivative) := by
      rw [commuting, commuting', add_comm]
    dsimp [remainder]
    simp only [map_sub]
    rw [equality]
    have cocycle' := cocycle
    rw [← difference] at cocycle'
    simp only [map_sub] at cocycle'
    linear_combination cocycle'
  have constant : remainder = Polynomial.C (remainder.eval 0) := by
    exact polynomial_periodic_constant remainder (-first) (neg_ne_zero.mpr first_ne)
      (fun point => by
        simpa only [Polynomial.taylor_eval] using
          congrArg (fun polynomial : Polynomial ℂ => polynomial.eval point) periodic)
  have right_expression : right = Polynomial.taylor (-second) antiderivative - antiderivative +
      Polynomial.C (remainder.eval 0) := by
    dsimp [remainder] at constant
    linear_combination constant
  have left_contraction : complexBernoulliOperator (degree + 1) first left =
      Polynomial.C (-first) * Polynomial.derivative antiderivative := by
    rw [← difference]
    exact complexBernoulliOperator_translation (degree + 1) first antiderivative
      antiderivative_bound
  have right_contraction : complexBernoulliOperator (degree + 1) second right =
      Polynomial.C (-second) * Polynomial.derivative antiderivative +
        Polynomial.C (remainder.eval 0) := by
    rw [right_expression, complexBernoulliOperator_add,
      complexBernoulliOperator_translation (degree + 1) second antiderivative
        antiderivative_bound, complexBernoulliOperator_C]
  rw [complexBernoulliOperator_degree_extend first left left_bound (Nat.le_succ degree)]
    at left_contraction
  rw [complexBernoulliOperator_degree_extend second right right_bound (Nat.le_succ degree)]
    at right_contraction
  refine ⟨-first * remainder.eval 0, ?_⟩
  rw [left_contraction, right_contraction, map_mul, map_neg, map_neg]
  ring

end TernaryPeriodPolynomials.PolynomialBernoulliDetection.Helpers
