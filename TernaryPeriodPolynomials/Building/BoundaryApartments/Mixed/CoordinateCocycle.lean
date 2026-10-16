module

public import TernaryPeriodPolynomials.Building.BoundaryApartments.ContractionNaturality

@[expose] public section


open GeneralEisenstein

noncomputable section


namespace TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers

open Homogeneous Matrix MvPolynomial

theorem mixedBernoulliCoordinate_of_radicalValues {degree : ℕ}
    {functional : EdgeChains →ₗ[ℂ] HomogeneousPoly degree}
    {cocycle : cocycles rationalLevel (rationalCoefficientComponent degree trivialCharacter)}
    (realizes : RealizesPathClass functional specialPaths cocycle)
    (levi : rationalLevel) (levi_line : levi.val ∈ Adelic.lineParabolic ℚ) :
    mixedBernoulliCoordinate cocycle levi.val =
      -radicalContractionMap degree
        (functional (mixedRadicalChain levi 1 0), functional (mixedRadicalChain levi 0 1)) := by
  have first := mixedBarEdge_of_levi realizes levi 1 0 levi_line
  have second := mixedBarEdge_of_levi realizes levi 0 1 levi_line
  simp only [Int.cast_one, Int.cast_zero] at first second
  unfold mixedBernoulliCoordinate
  rw [first, second, bernoulliOperator_neg, bernoulliOperator_neg]
  change X 2 * -bernoulliOperator degree (X 1) _ -
    X 1 * -bernoulliOperator degree (X 2) _ =
      -(X 2 * bernoulliOperator degree (X 1)
          (functional (mixedRadicalChain levi 1 0)).val -
        X 1 * bernoulliOperator degree (X 2)
          (functional (mixedRadicalChain levi 0 1)).val)
  unfold mixedRadicalChain
  rw [integralRadical_val, integralRadical_val]
  simp only [Int.cast_one, Int.cast_zero]
  ring

theorem mixedBernoulliCoordinate_product_contraction {degree : ℕ}
    {polynomial : HomogeneousPoly degree}
    {functional : EdgeChains →ₗ[ℂ] HomogeneousPoly degree}
    (functional_property : IsPolynomialFunctional polynomial functional)
    {cocycle : cocycles rationalLevel (rationalCoefficientComponent degree trivialCharacter)}
    (realizes : RealizesPathClass functional specialPaths cocycle)
    (first second : rationalLevel)
    (first_line : first.val ∈ Adelic.lineParabolic ℚ)
    (second_line : second.val ∈ Adelic.lineParabolic ℚ)
    (first_block : first.val.val 0 1 = 0 ∧ first.val.val 0 2 = 0)
    (second_block : second.val.val 0 1 = 0 ∧ second.val.val 0 2 = 0)
    (first_left first_right second_left second_right : ℤ)
    (first_conjugate : first⁻¹ * integralRadical 1 0 * first =
      integralRadical first_left first_right)
    (second_conjugate : first⁻¹ * integralRadical 0 1 * first =
      integralRadical second_left second_right) :
    mixedBernoulliCoordinate cocycle (first * second).val =
      mixedBernoulliCoordinate cocycle first.val -
        radicalContractionMap degree
          (rationalCoefficientComponent degree trivialCharacter first.val
            (functional (mixedRadicalChain second first_left first_right)),
           rationalCoefficientComponent degree trivialCharacter first.val
            (functional (mixedRadicalChain second second_left second_right))) := by
  have first_value := mixedBarEdge_levi_product functional_property realizes first second
    first_line second_line first_block second_block 1 0 first_left first_right first_conjugate
  have second_value := mixedBarEdge_levi_product functional_property realizes first second
    first_line second_line first_block second_block 0 1 second_left second_right second_conjugate
  simp only [Int.cast_one, Int.cast_zero] at first_value second_value
  unfold mixedBernoulliCoordinate
  rw [first_value, second_value]
  have operator_sub (parameter left right : Poly) : bernoulliOperator degree parameter (left - right) =
      bernoulliOperator degree parameter left - bernoulliOperator degree parameter right :=
    map_sub (bernoulliLinearMap degree parameter) left right
  rw [operator_sub, operator_sub]
  change X 2 * (bernoulliOperator degree (X 1) _ - bernoulliOperator degree (X 1) _) -
    X 1 * (bernoulliOperator degree (X 2) _ - bernoulliOperator degree (X 2) _) =
      X 2 * bernoulliOperator degree (X 1) _ - X 1 * bernoulliOperator degree (X 2) _ -
        (X 2 * bernoulliOperator degree (X 1) _ - X 1 * bernoulliOperator degree (X 2) _)
  ring

theorem binaryGenerator_integralRadical_conjugate (first second : ℤ) :
    arithmeticBinaryA⁻¹ * integralRadical first second * arithmeticBinaryA =
      integralRadical (first + 3 * second) (-first - 2 * second) ∧
    arithmeticBinaryB⁻¹ * integralRadical first second * arithmeticBinaryB =
      integralRadical (-first - 3 * second) second ∧
    arithmeticBinaryR⁻¹ * integralRadical first second * arithmeticBinaryR =
      integralRadical (-first) second := by
  constructor
  · apply Subtype.ext
    exact congrArg (fun matrix : badLineSubgroup => matrix.val) (badBinaryA_conjugate first second)
  · constructor
    · apply Subtype.ext
      exact congrArg (fun matrix : badLineSubgroup => matrix.val) (badBinaryB_conjugate first second)
    · apply Subtype.ext
      exact congrArg (fun matrix : badLineSubgroup => matrix.val) (badBinaryR_conjugate first second)

theorem mixedBernoulliCoordinate_generator_product {degree : ℕ}
    (degree_positive : 0 < degree) {polynomial : HomogeneousPoly degree}
    {functional : EdgeChains →ₗ[ℂ] HomogeneousPoly degree}
    (functional_property : IsPolynomialFunctional polynomial functional)
    {cocycle : cocycles rationalLevel (rationalCoefficientComponent degree trivialCharacter)}
    (realizes : RealizesPathClass functional specialPaths cocycle)
    (second : rationalLevel) (second_line : second.val ∈ Adelic.lineParabolic ℚ)
    (second_block : second.val.val 0 1 = 0 ∧ second.val.val 0 2 = 0) :
    mixedBernoulliCoordinate cocycle (arithmeticBinaryA * second).val =
      mixedBernoulliCoordinate cocycle binaryA +
        bind₁ ![X 0, -2 * X 1 + X 2, -3 * X 1 + X 2]
          (mixedBernoulliCoordinate cocycle second.val) ∧
    mixedBernoulliCoordinate cocycle (arithmeticBinaryB * second).val =
      mixedBernoulliCoordinate cocycle binaryB +
        bind₁ ![X 0, -X 1, -3 * X 1 + X 2]
          (mixedBernoulliCoordinate cocycle second.val) ∧
    mixedBernoulliCoordinate cocycle (arithmeticBinaryR * second).val =
      mixedBernoulliCoordinate cocycle binaryR +
        bind₁ ![X 0, -X 1, X 2]
          (mixedBernoulliCoordinate cocycle second.val) := by
  have actions := radicalContractionMap_crossed_generator_action degree_positive
    (fun first second_coordinate => functional (mixedRadicalChain second first second_coordinate))
    (mixedRadicalValue_crossed functional_property second second_line)
  have first_conjugates := binaryGenerator_integralRadical_conjugate 1 0
  have second_conjugates := binaryGenerator_integralRadical_conjugate 0 1
  have coordinate := mixedBernoulliCoordinate_of_radicalValues realizes second second_line
  constructor
  · rw [mixedBernoulliCoordinate_product_contraction functional_property realizes
      arithmeticBinaryA second (by rw [arithmeticBinaryA_val]; exact ⟨rfl, rfl⟩)
      second_line (by rw [arithmeticBinaryA_val]; exact ⟨rfl, rfl⟩) second_block 1 (-1) 3 (-2)
      (by simpa using first_conjugates.1) (by simpa using second_conjugates.1)]
    rw [arithmeticBinaryA_val, actions.1, coordinate, map_neg, sub_eq_add_neg]
  · constructor
    · rw [mixedBernoulliCoordinate_product_contraction functional_property realizes
        arithmeticBinaryB second (by rw [arithmeticBinaryB_val]; exact ⟨rfl, rfl⟩)
        second_line (by rw [arithmeticBinaryB_val]; exact ⟨rfl, rfl⟩) second_block (-1) 0 (-3) 1
        (by simpa using first_conjugates.2.1) (by simpa using second_conjugates.2.1)]
      rw [arithmeticBinaryB_val, actions.2.1, coordinate, map_neg, sub_eq_add_neg]
    · rw [mixedBernoulliCoordinate_product_contraction functional_property realizes
        arithmeticBinaryR second (by rw [arithmeticBinaryR_val]; exact ⟨rfl, rfl⟩)
        second_line (by rw [arithmeticBinaryR_val]; exact ⟨rfl, rfl⟩) second_block (-1) 0 0 1
        (by simpa using first_conjugates.2.2) (by simpa using second_conjugates.2.2)]
      rw [arithmeticBinaryR_val, actions.2.2, coordinate, map_neg, sub_eq_add_neg]

end TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers
