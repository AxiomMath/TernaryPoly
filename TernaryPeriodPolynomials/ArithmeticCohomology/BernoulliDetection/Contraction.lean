module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BernoulliDetection.Group

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic
open Matrix MvPolynomial

namespace TernaryPeriodPolynomials.PolynomialBernoulliDetection.Helpers

noncomputable def radicalContraction (degree : ℕ) (first second : Poly) : Poly :=
  X 2 * bernoulliOperator degree (X 1) first -
    X 1 * bernoulliOperator degree (X 2) second

noncomputable def primitiveCoordinate {degree : ℕ}
    (primitive : MaximalCochains degree trivialCharacter .line 1) : Poly :=
  radicalContraction degree (primitiveRadical primitive (1, 0)).val
    (primitiveRadical primitive (0, 1)).val

theorem radicalContraction_eval (degree : ℕ) (left right : Poly) (first second third : ℂ) :
    eval ![first, second, third] (radicalContraction degree left right) =
      third * (complexBernoulliOperator degree second (specializeFirst second third left)).eval first -
        second * (complexBernoulliOperator degree third (specializeFirst second third right)).eval first := by
  simp [radicalContraction, eval_bernoulliOperator, specializeFirst]

theorem primitiveCoordinate_constant_first {degree : ℕ}
    (cocycle : cocycles rationalLevel (rationalCoefficientComponent degree trivialCharacter))
    (primitive : MaximalCochains degree trivialCharacter .line 1)
    (primitive_eq : ∀ vertices flag, cocycle.val.val vertices =
      primitive.val ![vertices 1, vertices 2] flag -
        primitive.val ![vertices 0, vertices 2] flag +
        primitive.val ![vertices 0, vertices 1] flag)
    (pure : PureMixedBadLine cocycle) (first second third : ℂ) (second_ne : second ≠ 0) :
    eval ![first, second, third] (primitiveCoordinate primitive) =
      eval ![0, second, third] (primitiveCoordinate primitive) := by
  let lattice (pair : ℤ × ℤ) := specializeFirst second third (primitiveRadical primitive pair).val
  have lattice_eq := primitiveRadical_specialize_cocycle cocycle primitive primitive_eq pure second third
  have commutation := (lattice_eq (1, 0) (0, 1)).symm.trans
    ((congrArg lattice (add_comm (1, 0) (0, 1))).trans (lattice_eq (0, 1) (1, 0)))
  simp only [Int.cast_one, Int.cast_zero, one_mul, zero_mul, add_zero, zero_add] at commutation
  have commutation' : Polynomial.taylor (-second) (lattice (0, 1)) - lattice (0, 1) =
      Polynomial.taylor (-third) (lattice (1, 0)) - lattice (1, 0) := by
    linear_combination commutation
  obtain ⟨coefficient, equality⟩ := polynomial_radical_coordinate_constant degree second third
    second_ne (lattice (1, 0)) (lattice (0, 1))
    (specializeFirst_degree _ second third) (specializeFirst_degree _ second third) commutation'
  have evaluate (point : ℂ) := congrArg (fun polynomial : Polynomial ℂ => polynomial.eval point) equality
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C] at evaluate
  change eval ![first, second, third] (radicalContraction degree
    (primitiveRadical primitive (1, 0)).val (primitiveRadical primitive (0, 1)).val) = _
  rw [radicalContraction_eval, primitiveCoordinate, radicalContraction_eval]
  exact (evaluate first).trans (evaluate 0).symm

theorem polynomial_lattice_transformed_contraction (degree : ℕ) (second third : ℂ)
    (firstCoefficient secondCoefficient thirdCoefficient fourthCoefficient : ℤ)
    (lattice : ℤ × ℤ → Polynomial ℂ)
    (lattice_eq : ∀ firstPair secondPair, lattice (firstPair + secondPair) =
      lattice firstPair + Polynomial.taylor
        (-((firstPair.1 : ℂ) * second + (firstPair.2 : ℂ) * third)) (lattice secondPair))
    (degree_bound : ∀ pair, (lattice pair).natDegree ≤ degree)
    (second_ne : second ≠ 0) (first : ℂ) :
    ((firstCoefficient : ℂ) * second + (secondCoefficient : ℂ) * third) *
      (complexBernoulliOperator degree
        ((thirdCoefficient : ℂ) * second + (fourthCoefficient : ℂ) * third)
        (lattice (thirdCoefficient, fourthCoefficient))).eval first -
      ((thirdCoefficient : ℂ) * second + (fourthCoefficient : ℂ) * third) *
        (complexBernoulliOperator degree
          ((firstCoefficient : ℂ) * second + (secondCoefficient : ℂ) * third)
          (lattice (firstCoefficient, secondCoefficient))).eval first =
    ((firstCoefficient : ℂ) * (fourthCoefficient : ℂ) -
      (thirdCoefficient : ℂ) * (secondCoefficient : ℂ)) *
        (second * (complexBernoulliOperator degree third (lattice (0, 1))).eval first -
          third * (complexBernoulliOperator degree second (lattice (1, 0))).eval first) := by
  obtain ⟨antiderivative, coefficient, antiderivative_bound, expression⟩ :=
    polynomial_lattice_cocycle_expression degree second third second_ne lattice lattice_eq degree_bound
  have contraction (pair : ℤ × ℤ) :
      complexBernoulliOperator degree ((pair.1 : ℂ) * second + (pair.2 : ℂ) * third)
        (lattice pair) =
      Polynomial.C (-((pair.1 : ℂ) * second + (pair.2 : ℂ) * third)) *
        Polynomial.derivative antiderivative + Polynomial.C ((pair.2 : ℂ) * coefficient) := by
    rw [← complexBernoulliOperator_degree_extend _ _ (degree_bound pair) (Nat.le_succ degree),
      expression pair, complexBernoulliOperator_add,
      complexBernoulliOperator_translation (degree + 1) _ antiderivative antiderivative_bound,
      complexBernoulliOperator_C]
  have first_contraction := contraction (firstCoefficient, secondCoefficient)
  have second_contraction := contraction (thirdCoefficient, fourthCoefficient)
  have first_generator := contraction (1, 0)
  have second_generator := contraction (0, 1)
  simp only [Int.cast_zero, Int.cast_one, zero_mul, one_mul, add_zero, zero_add]
    at first_generator second_generator
  rw [first_contraction, second_contraction, first_generator, second_generator]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
  ring

end TernaryPeriodPolynomials.PolynomialBernoulliDetection.Helpers
