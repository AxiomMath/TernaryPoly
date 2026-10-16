module

public import TernaryPeriodPolynomials.Building.BoundaryApartments.Mixed.LeviCocycle
public import TernaryPeriodPolynomials.Building.BoundaryApartments.BoundaryDetection

@[expose] public section


open GeneralEisenstein

noncomputable section


namespace TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers

open Homogeneous Matrix MvPolynomial

theorem radicalContractionMap_transformed_normalForm {degree : ℕ}
    (matrix : badLineSubgroup)
    (crossed : ℤ → ℤ → HomogeneousPoly degree)
    (first_binary second_binary correction : HomogeneousPoly degree)
    (normal : ∀ first second : ℤ, crossed first second =
      first • first_binary + second • second_binary +
        (rationalCoefficientComponent degree trivialCharacter
          (badRadical first second).val correction - correction))
    (first_left first_right second_left second_right : ℤ)
    (first_conjugate : matrix⁻¹ * badRadical 1 0 * matrix =
      badRadical first_left first_right)
    (second_conjugate : matrix⁻¹ * badRadical 0 1 * matrix =
      badRadical second_left second_right) :
    radicalContractionMap degree
      (rationalCoefficientComponent degree trivialCharacter matrix.val
        (crossed first_left first_right),
       rationalCoefficientComponent degree trivialCharacter matrix.val
        (crossed second_left second_right)) =
      radicalContractionMap degree
        (rationalCoefficientComponent degree trivialCharacter matrix.val
          (first_left • first_binary + first_right • second_binary),
         rationalCoefficientComponent degree trivialCharacter matrix.val
          (second_left • first_binary + second_right • second_binary)) := by
  have commute (left right : ℤ) (radical : badLineSubgroup)
      (conjugate : matrix⁻¹ * radical * matrix = badRadical left right) :
      matrix.val * (badRadical left right).val = radical.val * matrix.val := by
    rw [← conjugate]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, ← mul_assoc, mul_inv_cancel, one_mul]
  have transformed (left right : ℤ) (radical : badLineSubgroup)
      (conjugate : matrix⁻¹ * radical * matrix = badRadical left right) :
      rationalCoefficientComponent degree trivialCharacter matrix.val (crossed left right) =
        rationalCoefficientComponent degree trivialCharacter matrix.val
          (left • first_binary + right • second_binary) +
        (rationalCoefficientComponent degree trivialCharacter radical.val
          (rationalCoefficientComponent degree trivialCharacter matrix.val correction) -
            rationalCoefficientComponent degree trivialCharacter matrix.val correction) := by
    rw [normal, map_add, map_sub, ← Module.End.mul_apply, ← map_mul,
      commute left right radical conjugate, map_mul, Module.End.mul_apply]
  rw [transformed first_left first_right (badRadical 1 0) first_conjugate,
    transformed second_left second_right (badRadical 0 1) second_conjugate]
  rw [show (badRadical 1 0).val = Adelic.lineUnipotent 1 0 by
    simpa only [Int.cast_one, Int.cast_zero] using badRadical_val 1 0,
    show (badRadical 0 1).val = Adelic.lineUnipotent 0 1 by
    simpa only [Int.cast_one, Int.cast_zero] using badRadical_val 0 1]
  have pair_add (first second third fourth : HomogeneousPoly degree) :
      (first + third, second + fourth) = (first, second) + (third, fourth) := rfl
  rw [pair_add, map_add, radicalContractionMap_coboundary, add_zero]

theorem radicalContractionMap_binary_generator (degree : ℕ)
    (first_binary second_binary : HomogeneousPoly degree)
    (first_derivative : pderiv 0 first_binary.val = 0)
    (second_derivative : pderiv 0 second_binary.val = 0) :
    radicalContractionMap degree
      (rationalCoefficientComponent degree trivialCharacter binaryA
        ((1 : ℤ) • first_binary + (-1 : ℤ) • second_binary),
       rationalCoefficientComponent degree trivialCharacter binaryA
        ((3 : ℤ) • first_binary + (-2 : ℤ) • second_binary)) =
      bind₁ ![X 0, -2 * X 1 + X 2, -3 * X 1 + X 2]
        (X 2 * first_binary.val - X 1 * second_binary.val) ∧
    radicalContractionMap degree
      (rationalCoefficientComponent degree trivialCharacter binaryB (-first_binary),
       rationalCoefficientComponent degree trivialCharacter binaryB
        (-3 • first_binary + second_binary)) =
      bind₁ ![X 0, -X 1, -3 * X 1 + X 2]
        (X 2 * first_binary.val - X 1 * second_binary.val) ∧
    radicalContractionMap degree
      (rationalCoefficientComponent degree trivialCharacter binaryR (-first_binary),
       rationalCoefficientComponent degree trivialCharacter binaryR second_binary) =
      bind₁ ![X 0, -X 1, X 2]
        (X 2 * first_binary.val - X 1 * second_binary.val) := by
  have first_preserved := binaryGenerator_preserves_binary degree first_binary first_derivative
  have second_preserved := binaryGenerator_preserves_binary degree second_binary second_derivative
  have derivative_linear (matrix : RationalGL3) (left right : ℤ)
      (first_zero : pderiv 0
        (rationalCoefficientComponent degree trivialCharacter matrix first_binary).val = 0)
      (second_zero : pderiv 0
        (rationalCoefficientComponent degree trivialCharacter matrix second_binary).val = 0) :
      pderiv 0 (rationalCoefficientComponent degree trivialCharacter matrix
        (left • first_binary + right • second_binary)).val = 0 := by
    simp only [map_add, map_zsmul, Submodule.coe_add, homogeneousPoly_coe_zsmul,
      map_add, map_zsmul, first_zero, second_zero, zsmul_zero, add_zero]
  constructor
  · rw [radicalContractionMap_binary]
    · simp [map_add, map_zsmul, Submodule.coe_add, rationalCoefficient_binaryA, zsmul_eq_mul]
      ring
    · exact derivative_linear binaryA 1 (-1) first_preserved.1 second_preserved.1
    · exact derivative_linear binaryA 3 (-2) first_preserved.1 second_preserved.1
  · constructor
    · rw [radicalContractionMap_binary]
      · simp [map_add, map_zsmul, Submodule.coe_add, rationalCoefficient_binaryB, zsmul_eq_mul]
        ring
      · simpa only [neg_one_zsmul, one_zsmul, zero_zsmul, add_zero] using
          derivative_linear binaryB (-1) 0 first_preserved.2.1 second_preserved.2.1
      · simpa only [one_zsmul] using
          derivative_linear binaryB (-3) 1 first_preserved.2.1 second_preserved.2.1
    · rw [radicalContractionMap_binary]
      · simp [rationalCoefficient_binaryR]
      · simpa only [neg_one_zsmul, zero_zsmul, add_zero] using
          derivative_linear binaryR (-1) 0 first_preserved.2.2 second_preserved.2.2
      · exact second_preserved.2.2

theorem radicalContractionMap_normalForm {degree : ℕ}
    (crossed : ℤ → ℤ → HomogeneousPoly degree)
    (first_binary second_binary correction : HomogeneousPoly degree)
    (first_derivative : pderiv 0 first_binary.val = 0)
    (second_derivative : pderiv 0 second_binary.val = 0)
    (normal : ∀ first second : ℤ, crossed first second =
      first • first_binary + second • second_binary +
        (rationalCoefficientComponent degree trivialCharacter
          (badRadical first second).val correction - correction)) :
    radicalContractionMap degree (crossed 1 0, crossed 0 1) =
      X 2 * first_binary.val - X 1 * second_binary.val := by
  rw [normal 1 0, normal 0 1]
  simp only [one_zsmul, zero_zsmul, zero_add, add_zero, badRadical_val,
    Int.cast_one, Int.cast_zero]
  have pair_add (first second third fourth : HomogeneousPoly degree) :
      (first + third, second + fourth) = (first, second) + (third, fourth) := rfl
  rw [pair_add, map_add, radicalContractionMap_coboundary, add_zero,
    radicalContractionMap_binary degree first_binary second_binary first_derivative second_derivative]

theorem radicalContractionMap_crossed_generator_action {degree : ℕ}
    (degree_positive : 0 < degree)
    (crossed : ℤ → ℤ → HomogeneousPoly degree)
    (relation : ∀ first second third fourth : ℤ,
      crossed (first + third) (second + fourth) =
        rationalCoefficientComponent degree trivialCharacter
          (integralRadical first second).val (crossed third fourth) + crossed first second) :
    radicalContractionMap degree
      (rationalCoefficientComponent degree trivialCharacter binaryA (crossed 1 (-1)),
       rationalCoefficientComponent degree trivialCharacter binaryA (crossed 3 (-2))) =
      bind₁ ![X 0, -2 * X 1 + X 2, -3 * X 1 + X 2]
        (radicalContractionMap degree (crossed 1 0, crossed 0 1)) ∧
    radicalContractionMap degree
      (rationalCoefficientComponent degree trivialCharacter binaryB (crossed (-1) 0),
       rationalCoefficientComponent degree trivialCharacter binaryB (crossed (-3) 1)) =
      bind₁ ![X 0, -X 1, -3 * X 1 + X 2]
        (radicalContractionMap degree (crossed 1 0, crossed 0 1)) ∧
    radicalContractionMap degree
      (rationalCoefficientComponent degree trivialCharacter binaryR (crossed (-1) 0),
       rationalCoefficientComponent degree trivialCharacter binaryR (crossed 0 1)) =
      bind₁ ![X 0, -X 1, X 2]
        (radicalContractionMap degree (crossed 1 0, crossed 0 1)) := by
  obtain ⟨first_binary, second_binary, correction, first_derivative, second_derivative, normal⟩ :=
    radicalCrossed_binary_normalForm degree_positive crossed relation
  have normal_bad (first second : ℤ) : crossed first second =
      first • first_binary + second • second_binary +
        (rationalCoefficientComponent degree trivialCharacter
          (badRadical first second).val correction - correction) := normal first second
  have contraction := radicalContractionMap_normalForm crossed first_binary second_binary
    correction first_derivative second_derivative normal_bad
  have transformed := radicalContractionMap_binary_generator degree first_binary second_binary
    first_derivative second_derivative
  have first_contraction := radicalContractionMap_transformed_normalForm badBinaryA crossed
    first_binary second_binary correction normal_bad 1 (-1) 3 (-2)
    (by simpa using badBinaryA_conjugate 1 0) (by simpa using badBinaryA_conjugate 0 1)
  have second_contraction := radicalContractionMap_transformed_normalForm badBinaryB crossed
    first_binary second_binary correction normal_bad (-1) 0 (-3) 1
    (by simpa using badBinaryB_conjugate 1 0) (by simpa using badBinaryB_conjugate 0 1)
  have third_contraction := radicalContractionMap_transformed_normalForm badBinaryR crossed
    first_binary second_binary correction normal_bad (-1) 0 0 1
    (by simpa using badBinaryR_conjugate 1 0) (by simpa using badBinaryR_conjugate 0 1)
  rw [badBinaryA_val] at first_contraction
  rw [badBinaryB_val] at second_contraction
  rw [badBinaryR_val] at third_contraction
  simp only [neg_one_zsmul, zero_zsmul, one_zsmul, add_zero] at second_contraction
  simp only [neg_one_zsmul, zero_zsmul, one_zsmul, add_zero, zero_add] at third_contraction
  rw [contraction]
  constructor
  · exact first_contraction.trans transformed.1
  · constructor
    · exact second_contraction.trans transformed.2.1
    · exact third_contraction.trans transformed.2.2

end TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers
