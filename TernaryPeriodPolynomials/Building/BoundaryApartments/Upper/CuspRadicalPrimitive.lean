module

public import TernaryPeriodPolynomials.Building.BoundaryApartments.Upper.TranslationRadical

@[expose] public section


open GeneralEisenstein

noncomputable section


namespace TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers

open Homogeneous MvPolynomial

def binaryRadicalValue {degree : ℕ} (first second : HomogeneousPoly degree)
    (left right : ℤ) : HomogeneousPoly degree := left • first + right • second

theorem binaryRadicalValue_binary {degree : ℕ} (first second : HomogeneousPoly degree)
    (first_binary : pderiv 0 first.val = 0) (second_binary : pderiv 0 second.val = 0)
    (left right : ℤ) : pderiv 0 (binaryRadicalValue first second left right).val = 0 := by
  simp only [binaryRadicalValue, Submodule.coe_add, homogeneousPoly_coe_zsmul,
    map_add, map_zsmul, first_binary, second_binary, zsmul_zero, add_zero]

theorem binaryRadicalValue_crossed {degree : ℕ} (first second : HomogeneousPoly degree)
    (first_binary : pderiv 0 first.val = 0) (second_binary : pderiv 0 second.val = 0)
    (left right next_left next_right : ℤ) :
    binaryRadicalValue first second (left + next_left) (right + next_right) =
      rationalCoefficientComponent degree trivialCharacter (integralRadical left right).val
        (binaryRadicalValue first second next_left next_right) +
          binaryRadicalValue first second left right := by
  rw [integralRadical_val, rationalCoefficient_binary_fixed _
    (binaryRadicalValue_binary first second first_binary second_binary next_left next_right)]
  simp only [binaryRadicalValue, add_zsmul]
  abel

theorem upperCusp_exists_radicalCorrection {degree : ℕ}
    (degree_positive : 0 < degree) {polynomial : HomogeneousPoly degree}
    (solution : SymmetricSolution polynomial)
    {functional : EdgeChains →ₗ[ℂ] HomogeneousPoly degree}
    (functional_property : IsPolynomialFunctional polynomial functional)
    {cocycle : cocycles rationalLevel (rationalCoefficientComponent degree trivialCharacter)}
    (realizes : RealizesPathClass functional specialPaths cocycle) :
    ∃ first second correction : HomogeneousPoly degree,
      pderiv 0 first.val = 0 ∧ pderiv 0 second.val = 0 ∧
      rationalCoefficientComponent degree trivialCharacter binaryR (-first) = first ∧
      rationalCoefficientComponent degree trivialCharacter binaryR second = second ∧
      ∀ left right : ℤ,
        mixedBarEdge cocycle upperCuspTranslation.val
            (Adelic.lineUnipotent (left : ℚ) (right : ℚ)) =
          (rationalCoefficientComponent degree trivialCharacter upperCuspTranslation.val
            (binaryRadicalValue first second left (left + right)) -
              binaryRadicalValue first second left right +
            (rationalCoefficientComponent degree trivialCharacter
              (integralRadical left right).val correction - correction)).val := by
  obtain ⟨primitive, primitive_binary, primitive_coordinate, primitive_reflection⟩ :=
    upperCuspCoordinate_exists_reflectionPrimitive degree_positive solution functional_property realizes
  obtain ⟨first, second, first_binary, second_binary, coordinate, first_reflection,
      second_reflection⟩ := radicalCoordinate_reflection_surjective degree primitive
        primitive_binary primitive_reflection
  let action := rationalCoefficientComponent degree trivialCharacter upperCuspTranslation.val
  let difference_first := action (first + second) - first
  let difference_second := action second - second
  have sum_binary : pderiv 0 (first + second).val = 0 := by
    change pderiv 0 (first.val + second.val) = 0
    rw [map_add, first_binary, second_binary, add_zero]
  have first_preserved := upperCuspTranslation_preserves_binary degree (first + second) sum_binary
  have second_preserved := upperCuspTranslation_preserves_binary degree second second_binary
  change pderiv 0 (action (first + second)).val = 0 at first_preserved
  change pderiv 0 (action second).val = 0 at second_preserved
  have difference_first_binary : pderiv 0 difference_first.val = 0 := by
    change pderiv 0 ((action (first + second)).val - first.val) = 0
    rw [map_sub, first_preserved, first_binary, sub_self]
  have difference_second_binary : pderiv 0 difference_second.val = 0 := by
    change pderiv 0 ((action second).val - second.val) = 0
    rw [map_sub, second_preserved, second_binary, sub_self]
  have difference_coordinate :
      radicalContractionMap degree (difference_first, difference_second) =
        mixedBernoulliCoordinate cocycle upperCuspTranslation.val := by
    change radicalContractionMap degree
      ((action (first + second), action second) - (first, second)) = _
    rw [map_sub, radicalContractionMap_binary_upperTranslation degree first second
      first_binary second_binary, coordinate, primitive_coordinate]
  let remainder (left right : ℤ) : HomogeneousPoly degree :=
    -functional (mixedRadicalChain upperCuspTranslation left right) -
      binaryRadicalValue difference_first difference_second left right
  have crossed (left right next_left next_right : ℤ) :
      remainder (left + next_left) (right + next_right) =
        rationalCoefficientComponent degree trivialCharacter (integralRadical left right).val
          (remainder next_left next_right) + remainder left right := by
    simp only [remainder, mixedRadicalValue_crossed functional_property
      upperCuspTranslation upperCuspTranslation_line,
      binaryRadicalValue_crossed difference_first difference_second
        difference_first_binary difference_second_binary, map_sub, map_neg]
    abel
  have remainder_coordinate : radicalContractionMap degree (remainder 1 0, remainder 0 1) = 0 := by
    have mixed_coordinate := mixedBernoulliCoordinate_of_radicalValues realizes
      upperCuspTranslation upperCuspTranslation_line
    change mixedBernoulliCoordinate cocycle upperCuspTranslation.val =
      -radicalContractionMap degree
        (functional (mixedRadicalChain upperCuspTranslation 1 0),
         functional (mixedRadicalChain upperCuspTranslation 0 1)) at mixed_coordinate
    simp only [remainder, binaryRadicalValue, one_zsmul, zero_zsmul, add_zero, zero_add]
    change radicalContractionMap degree
      (-(functional (mixedRadicalChain upperCuspTranslation 1 0),
          functional (mixedRadicalChain upperCuspTranslation 0 1)) -
        (difference_first, difference_second)) = 0
    rw [map_sub, map_neg, ← mixed_coordinate, difference_coordinate, sub_self]
  obtain ⟨correction, correction_eq⟩ := radicalCrossed_zero_exists_primitive degree_positive
    remainder crossed remainder_coordinate
  refine ⟨first, second, correction, first_binary, second_binary, first_reflection,
    second_reflection, ?_⟩
  intro left right
  rw [mixedBarEdge_of_levi realizes upperCuspTranslation left right upperCuspTranslation_line]
  rw [← integralRadical_val left right]
  have normal : -functional (mixedRadicalChain upperCuspTranslation left right) =
      binaryRadicalValue difference_first difference_second left right +
        (rationalCoefficientComponent degree trivialCharacter
          (integralRadical left right).val correction - correction) := by
    exact (sub_eq_iff_eq_add.mp (correction_eq left right)).trans (add_comm _ _)
  change (-functional (mixedRadicalChain upperCuspTranslation left right)).val = _
  rw [normal]
  apply congrArg Subtype.val
  have difference : binaryRadicalValue difference_first difference_second left right =
      action (binaryRadicalValue first second left (left + right)) -
        binaryRadicalValue first second left right := by
    simp only [binaryRadicalValue, difference_first, difference_second, map_add,
      map_zsmul, add_zsmul, zsmul_sub, zsmul_add]
    abel
  rw [difference]

end TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers
