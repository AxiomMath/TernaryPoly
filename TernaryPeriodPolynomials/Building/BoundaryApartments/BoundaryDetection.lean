module

public import TernaryPeriodPolynomials.Building.BoundaryApartments.BinaryGeneratorAction

@[expose] public section


open GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers

open Homogeneous Matrix MvPolynomial

theorem binaryGenerator_preserves_binary (degree : ℕ) (polynomial : HomogeneousPoly degree)
    (binary : pderiv 0 polynomial.val = 0) :
    pderiv 0 (rationalCoefficientComponent degree trivialCharacter binaryA polynomial).val = 0 ∧
    pderiv 0 (rationalCoefficientComponent degree trivialCharacter binaryB polynomial).val = 0 ∧
    pderiv 0 (rationalCoefficientComponent degree trivialCharacter binaryR polynomial).val = 0 := by
  have first : pderiv (0 : Fin 3)
      (bind₁ (![X 0, -2 * X 1 + X 2, -3 * X 1 + X 2] : Fin 3 → Poly) polynomial.val) = 0 := by
    rw [pderiv_bind_commutes ![X 0, -2 * X 1 + X 2, -3 * X 1 + X 2]
      (by intro index; fin_cases index <;> simp [← map_ofNat C]) polynomial.val, binary, map_zero]
  have second : pderiv (0 : Fin 3)
      (bind₁ (![X 0, -X 1, -3 * X 1 + X 2] : Fin 3 → Poly) polynomial.val) = 0 := by
    rw [pderiv_bind_commutes ![X 0, -X 1, -3 * X 1 + X 2]
      (by intro index; fin_cases index <;> simp [← map_ofNat C]) polynomial.val, binary, map_zero]
  have third : pderiv (0 : Fin 3)
      (bind₁ (![X 0, -X 1, X 2] : Fin 3 → Poly) polynomial.val) = 0 := by
    rw [pderiv_bind_commutes ![X 0, -X 1, X 2]
      (by intro index; fin_cases index <;> simp) polynomial.val, binary, map_zero]
  constructor
  · rw [rationalCoefficient_binaryA]
    exact first
  · constructor
    · rw [rationalCoefficient_binaryB, map_neg]
      simpa only [neg_zero] using congrArg Neg.neg second
    · rw [rationalCoefficient_binaryR, map_neg]
      simpa only [neg_zero] using congrArg Neg.neg third

theorem homogeneousPoly_coe_zsmul (degree : ℕ) (integer : ℤ) (polynomial : HomogeneousPoly degree) :
    (integer • polynomial).val = integer • polynomial.val :=
  map_zsmul (HomogeneousPoly degree).subtype integer polynomial

theorem radicalContractionMap_binary (degree : ℕ) (first second : HomogeneousPoly degree)
    (first_binary : pderiv 0 first.val = 0) (second_binary : pderiv 0 second.val = 0) :
    radicalContractionMap degree (first, second) = X 2 * first.val - X 1 * second.val := by
  change X 2 * bernoulliOperator degree (X 1) first.val -
    X 1 * bernoulliOperator degree (X 2) second.val = _
  rw [bernoulliOperator_binary _ _ _ first_binary, bernoulliOperator_binary _ _ _ second_binary]

theorem binaryPrimitive_generator_coordinates {degree : ℕ}
    (cocycle : cocycles rationalLevel (rationalCoefficientComponent degree trivialCharacter))
    (primitive : badLineSubgroup → HomogeneousPoly degree)
    (differential : ∀ first second : badLineSubgroup,
      cocycle.val.val ![1, first.val, (first * second).val] =
        rationalCoefficientComponent degree trivialCharacter first.val (primitive second) -
          primitive (first * second) + primitive first)
    (first_binary second_binary : HomogeneousPoly degree)
    (first_derivative : pderiv 0 first_binary.val = 0)
    (second_derivative : pderiv 0 second_binary.val = 0)
    (normal : ∀ first second : ℤ,
      primitive (badRadical first second) = first • first_binary + second • second_binary) :
    let binary_coordinate := X 2 * first_binary.val - X 1 * second_binary.val
    mixedBernoulliCoordinate cocycle binaryA =
        bind₁ ![X 0, -2 * X 1 + X 2, -3 * X 1 + X 2] binary_coordinate - binary_coordinate ∧
    mixedBernoulliCoordinate cocycle binaryB =
        bind₁ ![X 0, -X 1, -3 * X 1 + X 2] binary_coordinate - binary_coordinate ∧
    mixedBernoulliCoordinate cocycle binaryR =
        bind₁ ![X 0, -X 1, X 2] binary_coordinate - binary_coordinate := by
  have first_preserved := binaryGenerator_preserves_binary degree first_binary first_derivative
  have second_preserved := binaryGenerator_preserves_binary degree second_binary second_derivative
  have coordinate_A := mixedBernoulliCoordinate_of_binaryPrimitive cocycle primitive differential
    first_binary second_binary normal badBinaryA 1 (-1) 3 (-2)
    (by simpa using badBinaryA_conjugate 1 0) (by simpa using badBinaryA_conjugate 0 1)
  have coordinate_B := mixedBernoulliCoordinate_of_binaryPrimitive cocycle primitive differential
    first_binary second_binary normal badBinaryB (-1) 0 (-3) 1
    (by simpa using badBinaryB_conjugate 1 0) (by simpa using badBinaryB_conjugate 0 1)
  have coordinate_R := mixedBernoulliCoordinate_of_binaryPrimitive cocycle primitive differential
    first_binary second_binary normal badBinaryR (-1) 0 0 1
    (by simpa using badBinaryR_conjugate 1 0) (by simpa using badBinaryR_conjugate 0 1)
  rw [badBinaryA_val] at coordinate_A
  rw [badBinaryB_val] at coordinate_B
  rw [badBinaryR_val] at coordinate_R
  have derivative_linear (matrix : RationalGL3) (first second : ℤ)
      (preserves_first : pderiv 0
        (rationalCoefficientComponent degree trivialCharacter matrix first_binary).val = 0)
      (preserves_second : pderiv 0
        (rationalCoefficientComponent degree trivialCharacter matrix second_binary).val = 0)
      (subtracted : HomogeneousPoly degree) (subtracted_binary : pderiv 0 subtracted.val = 0) :
      pderiv 0 (rationalCoefficientComponent degree trivialCharacter matrix
        (first • first_binary + second • second_binary) - subtracted).val = 0 := by
    simp only [map_add, map_zsmul, Submodule.coe_sub, Submodule.coe_add,
      homogeneousPoly_coe_zsmul, map_zsmul, preserves_first, preserves_second, subtracted_binary,
      zsmul_zero, add_zero, sub_zero, map_sub]
  constructor
  · rw [coordinate_A, radicalContractionMap_binary]
    · simp [map_add, map_zsmul, Submodule.coe_add, rationalCoefficient_binaryA, zsmul_eq_mul]
      ring
    · exact derivative_linear binaryA 1 (-1) first_preserved.1 second_preserved.1
        first_binary first_derivative
    · exact derivative_linear binaryA 3 (-2) first_preserved.1 second_preserved.1
        second_binary second_derivative
  · constructor
    · rw [coordinate_B, radicalContractionMap_binary]
      · simp [map_add, map_zsmul, Submodule.coe_add, rationalCoefficient_binaryB, zsmul_eq_mul]
        ring
      · exact derivative_linear binaryB (-1) 0 first_preserved.2.1 second_preserved.2.1
          first_binary first_derivative
      · exact derivative_linear binaryB (-3) 1 first_preserved.2.1 second_preserved.2.1
          second_binary second_derivative
    · rw [coordinate_R, radicalContractionMap_binary]
      · simp [rationalCoefficient_binaryR]
        ring
      · exact derivative_linear binaryR (-1) 0 first_preserved.2.2 second_preserved.2.2
          first_binary first_derivative
      · exact derivative_linear binaryR 0 1 first_preserved.2.2 second_preserved.2.2
          second_binary second_derivative

theorem polynomialValue_binaryB_invariant (polynomial : Poly)
    (invariant : bind₁ (![X 0, -X 1, -3 * X 1 + X 2] : Fin 3 → Poly) polynomial = polynomial)
    (second third : ℂ) :
    polynomialValue polynomial 0 (-second) (third - 3 * second) =
      polynomialValue polynomial 0 second third := by
  have evaluated := congrArg (fun value : Poly => polynomialValue value 0 second third) invariant
  rw [polynomialValue_bind] at evaluated
  have coordinates : (fun index => polynomialValue
      ((![X 0, -X 1, -3 * X 1 + X 2] : Fin 3 → Poly) index) 0 second third) =
      ![0, -second, third - 3 * second] := by
    funext index
    fin_cases index <;> simp [polynomialValue]
    ring
  rw [coordinates] at evaluated
  exact evaluated

theorem polynomialValue_binaryR_invariant (polynomial : Poly)
    (invariant : bind₁ (![X 0, -X 1, X 2] : Fin 3 → Poly) polynomial = polynomial)
    (second third : ℂ) :
    polynomialValue polynomial 0 (-second) third = polynomialValue polynomial 0 second third := by
  have evaluated := congrArg (fun value : Poly => polynomialValue value 0 second third) invariant
  rw [polynomialValue_bind] at evaluated
  have coordinates : (fun index => polynomialValue
      ((![X 0, -X 1, X 2] : Fin 3 → Poly) index) 0 second third) = ![0, -second, third] := by
    funext index
    fin_cases index <;> simp [polynomialValue]
  rw [coordinates] at evaluated
  exact evaluated

theorem bernoulliObstruction_of_lineClass_zero {degree : ℕ} (degree_positive : 0 < degree)
    {polynomial : HomogeneousPoly degree} (solution : SymmetricSolution polynomial)
    (cocycle : cocycles rationalLevel (rationalCoefficientComponent degree trivialCharacter))
    (pure : PureMixedBadLine cocycle)
    (coordinate_A : mixedBernoulliCoordinate cocycle binaryA = -bernoulliObstruction polynomial)
    (coordinate_B : mixedBernoulliCoordinate cocycle binaryB = 0)
    (coordinate_R : mixedBernoulliCoordinate cocycle binaryR = 0)
    (zero_class : (globalCoordinates degree trivialCharacter cocycle).2 = 0) :
    bernoulliObstruction polynomial = 0 := by
  obtain ⟨primitive, first_binary, second_binary, differential,
    first_derivative, second_derivative, normal⟩ :=
      lineClass_zero_exists_binaryPrimitive degree_positive cocycle pure zero_class
  obtain ⟨first_coordinate, second_coordinate, third_coordinate⟩ :=
    binaryPrimitive_generator_coordinates cocycle primitive differential first_binary second_binary
      first_derivative second_derivative normal
  let binary_polynomial : Poly := X 2 * first_binary.val - X 1 * second_binary.val
  have homogeneous : binary_polynomial.IsHomogeneous (degree + 1) := by
    simpa only [binary_polynomial, Nat.add_comm] using
      ((isHomogeneous_X ℂ 2).mul first_binary.property).sub
        ((isHomogeneous_X ℂ 1).mul second_binary.property)
  let binary_primitive : HomogeneousPoly (degree + 1) := ⟨binary_polynomial, homogeneous⟩
  have binary : pderiv 0 binary_polynomial = 0 := by
    simp only [binary_polynomial, map_sub, pderiv_mul,
      pderiv_X_of_ne (by decide : (1 : Fin 3) ≠ 0),
      pderiv_X_of_ne (by decide : (2 : Fin 3) ≠ 0), first_derivative, second_derivative,
      zero_mul, mul_zero, add_zero, sub_zero]
  have invariant_B : bind₁ (![X 0, -X 1, -3 * X 1 + X 2] : Fin 3 → Poly)
      binary_polynomial = binary_polynomial := by
    apply sub_eq_zero.mp
    exact second_coordinate.symm.trans coordinate_B
  have invariant_R : bind₁ (![X 0, -X 1, X 2] : Fin 3 → Poly)
      binary_polynomial = binary_polynomial := by
    apply sub_eq_zero.mp
    exact third_coordinate.symm.trans coordinate_R
  have shear (second third : ℂ) : polynomialValue binary_polynomial 0 second (third + 3 * second) =
      polynomialValue binary_polynomial 0 second third := by
    have reflected := polynomialValue_binaryB_invariant binary_polynomial invariant_B (-second) third
    simp only [neg_neg, mul_neg, sub_neg_eq_add] at reflected
    exact reflected.trans (polynomialValue_binaryR_invariant binary_polynomial invariant_R second third)
  have obstruction_coordinate : bernoulliObstruction polynomial = binary_polynomial -
      bind₁ ![X 0, -2 * X 1 + X 2, -3 * X 1 + X 2] binary_polynomial := by
    have equality := first_coordinate.symm.trans coordinate_A
    have negated := congrArg Neg.neg equality
    rw [neg_neg] at negated
    rw [← negated]
    change -(bind₁ (![X 0, -2 * X 1 + X 2, -3 * X 1 + X 2] : Fin 3 → Poly)
      binary_polynomial - binary_polynomial) = _
    abel
  exact binaryDetection_of_primitive (by omega : 0 < degree + 1) binary_primitive
    (derivative_zero_eval_binary binary_polynomial binary) shear obstruction_coordinate
    (bernoulliObstruction_goodBoundary solution)

end TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers
