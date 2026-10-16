module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BernoulliDetection.Contraction

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic
open Matrix MvPolynomial

namespace TernaryPeriodPolynomials.PolynomialBernoulliDetection.Helpers

theorem specializeFirst_add (second third : ℂ) (left right : Poly) :
    specializeFirst second third (left + right) =
      specializeFirst second third left + specializeFirst second third right := by
  simp [specializeFirst]

theorem specializeFirst_sub (second third : ℂ) (left right : Poly) :
    specializeFirst second third (left - right) =
      specializeFirst second third left - specializeFirst second third right := by
  simp [specializeFirst]

theorem specializeFirst_smul (second third scalar : ℂ) (polynomial : Poly) :
    specializeFirst second third (scalar • polynomial) =
      Polynomial.C scalar * specializeFirst second third polynomial := by
  apply Polynomial.funext
  intro first
  simp [specializeFirst_eval, Algebra.smul_def]

theorem radicalContraction_coboundary {degree : ℕ}
    (polynomial : HomogeneousPoly degree) (first second third : ℂ) :
    eval ![first, second, third]
      (radicalContraction degree
        (polynomial.val - (rationalCoefficientComponent degree trivialCharacter
          (lineUnipotent 1 0) polynomial).val)
        (polynomial.val - (rationalCoefficientComponent degree trivialCharacter
          (lineUnipotent 0 1) polynomial).val)) = 0 := by
  rw [radicalContraction_eval, specializeFirst_sub, specializeFirst_sub,
    specializeFirst_radical, specializeFirst_radical]
  simp only [Rat.cast_one, Rat.cast_zero, one_mul, zero_mul, add_zero, zero_add]
  have left_eq := complexBernoulliOperator_translation degree second
    (specializeFirst second third polynomial.val) (specializeFirst_degree polynomial second third)
  have right_eq := complexBernoulliOperator_translation degree third
    (specializeFirst second third polynomial.val) (specializeFirst_degree polynomial second third)
  have reverse_difference (parameter : ℂ) :
      complexBernoulliOperator degree parameter
        (specializeFirst second third polynomial.val -
          Polynomial.taylor (-parameter) (specializeFirst second third polynomial.val)) =
      -complexBernoulliOperator degree parameter
        (Polynomial.taylor (-parameter) (specializeFirst second third polynomial.val) -
          specializeFirst second third polynomial.val) := by
    rw [complexBernoulliOperator_sub, complexBernoulliOperator_sub]
    abel
  rw [reverse_difference, reverse_difference, left_eq, right_eq]
  simp only [Polynomial.eval_neg, Polynomial.eval_mul, Polynomial.eval_C]
  ring

theorem mixed_coordinate_eval {degree : ℕ}
    (cocycle : cocycles rationalLevel (rationalCoefficientComponent degree trivialCharacter))
    (primitive : MaximalCochains degree trivialCharacter .line 1)
    (primitive_eq : ∀ vertices flag, cocycle.val.val vertices =
      primitive.val ![vertices 1, vertices 2] flag -
        primitive.val ![vertices 0, vertices 2] flag +
        primitive.val ![vertices 0, vertices 1] flag)
    (pure : PureMixedBadLine cocycle) (levi : rationalLevel)
    (levi_fixed : levi.val⁻¹ • (QuotientGroup.mk 1 : Flags .line) = QuotientGroup.mk 1)
    (firstCoefficient secondCoefficient thirdCoefficient fourthCoefficient : ℤ)
    (first_conjugate : levi.val⁻¹ * lineUnipotent 1 0 * levi.val =
      lineUnipotent (firstCoefficient : ℚ) (secondCoefficient : ℚ))
    (second_conjugate : levi.val⁻¹ * lineUnipotent 0 1 * levi.val =
      lineUnipotent (thirdCoefficient : ℚ) (fourthCoefficient : ℚ))
    (first second third transformedSecond transformedThird scalar : ℂ)
    (transformed_ne : transformedSecond ≠ 0)
    (first_parameter : (firstCoefficient : ℂ) * transformedSecond +
      (secondCoefficient : ℂ) * transformedThird = second)
    (second_parameter : (thirdCoefficient : ℂ) * transformedSecond +
      (fourthCoefficient : ℂ) * transformedThird = third)
    (determinant_eq : scalar * ((firstCoefficient : ℂ) * (fourthCoefficient : ℂ) -
      (thirdCoefficient : ℂ) * (secondCoefficient : ℂ)) = 1)
    (specialization : ∀ polynomial : HomogeneousPoly degree,
      specializeFirst second third
        (rationalCoefficientComponent degree trivialCharacter levi.val polynomial).val =
      Polynomial.C scalar * specializeFirst transformedSecond transformedThird polynomial.val) :
    eval ![first, second, third] (mixedBernoulliCoordinate cocycle levi.val) =
      eval ![first, transformedSecond, transformedThird] (primitiveCoordinate primitive) -
        eval ![first, second, third] (primitiveCoordinate primitive) := by
  let leviPrimitive := primitive.val ![1, levi.val] (QuotientGroup.mk 1)
  let firstRadical : rationalLevel := ⟨lineUnipotent 1 0, line_radical_rational_mem 1 0⟩
  let secondRadical : rationalLevel := ⟨lineUnipotent 0 1, line_radical_rational_mem 0 1⟩
  have first_edge := line_primitive_mixed cocycle primitive primitive_eq levi firstRadical
    (QuotientGroup.mk 1) levi_fixed (line_radical_flag_fixed 1 0)
  have second_edge := line_primitive_mixed cocycle primitive primitive_eq levi secondRadical
    (QuotientGroup.mk 1) levi_fixed (line_radical_flag_fixed 0 1)
  change mixedBarEdge cocycle levi.val (lineUnipotent 1 0) = _ at first_edge
  change mixedBarEdge cocycle levi.val (lineUnipotent 0 1) = _ at second_edge
  rw [first_conjugate] at first_edge
  rw [second_conjugate] at second_edge
  change mixedBarEdge cocycle levi.val (lineUnipotent 1 0) =
    (rationalCoefficientComponent degree trivialCharacter levi.val
      (primitiveRadical primitive (firstCoefficient, secondCoefficient))).val -
    (primitiveRadical primitive (1, 0)).val + leviPrimitive.val -
    (rationalCoefficientComponent degree trivialCharacter (lineUnipotent 1 0)
      leviPrimitive).val at first_edge
  change mixedBarEdge cocycle levi.val (lineUnipotent 0 1) =
    (rationalCoefficientComponent degree trivialCharacter levi.val
      (primitiveRadical primitive (thirdCoefficient, fourthCoefficient))).val -
    (primitiveRadical primitive (0, 1)).val + leviPrimitive.val -
    (rationalCoefficientComponent degree trivialCharacter (lineUnipotent 0 1)
      leviPrimitive).val at second_edge
  have expression : mixedBernoulliCoordinate cocycle levi.val =
      radicalContraction degree
        (rationalCoefficientComponent degree trivialCharacter levi.val
          (primitiveRadical primitive (firstCoefficient, secondCoefficient))).val
        (rationalCoefficientComponent degree trivialCharacter levi.val
          (primitiveRadical primitive (thirdCoefficient, fourthCoefficient))).val -
      primitiveCoordinate primitive +
      radicalContraction degree
        (leviPrimitive.val - (rationalCoefficientComponent degree trivialCharacter
          (lineUnipotent 1 0) leviPrimitive).val)
        (leviPrimitive.val - (rationalCoefficientComponent degree trivialCharacter
          (lineUnipotent 0 1) leviPrimitive).val) := by
    simp only [mixedBernoulliCoordinate, first_edge, second_edge,
      radicalContraction, primitiveCoordinate,
      bernoulliOperator_add, bernoulliOperator_sub]
    ring
  rw [expression, map_add, map_sub, radicalContraction_coboundary, add_zero]
  apply congrArg (fun value : ℂ => value -
    eval ![first, second, third] (primitiveCoordinate primitive))
  rw [radicalContraction_eval, specialization, specialization,
    complexBernoulliOperator_C_mul, complexBernoulliOperator_C_mul]
  simp only [Polynomial.eval_mul, Polynomial.eval_C]
  rw [primitiveCoordinate, radicalContraction_eval]
  have transformed := polynomial_lattice_transformed_contraction degree
    transformedSecond transformedThird firstCoefficient secondCoefficient
    thirdCoefficient fourthCoefficient
    (fun pair => specializeFirst transformedSecond transformedThird
      (primitiveRadical primitive pair).val)
    (primitiveRadical_specialize_cocycle cocycle primitive primitive_eq pure
      transformedSecond transformedThird)
    (fun pair => specializeFirst_degree (primitiveRadical primitive pair)
      transformedSecond transformedThird) transformed_ne first
  rw [first_parameter, second_parameter] at transformed
  have scaled := congrArg (fun value : ℂ => scalar * value) transformed
  rw [← mul_assoc, determinant_eq, one_mul] at scaled
  linear_combination -scaled

end TernaryPeriodPolynomials.PolynomialBernoulliDetection.Helpers
