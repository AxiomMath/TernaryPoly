module

public import TernaryPeriodPolynomials.Building.BoundaryApartments.Radical.Exactness

@[expose] public section


open GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers

open MvPolynomial

def binaryProjection : Poly →ₐ[ℂ] Poly := bind₁ ![0, X 1, X 2]

theorem binaryProjection_pderiv (polynomial : Poly) :
    pderiv 0 (binaryProjection polynomial) = 0 := by
  induction polynomial using MvPolynomial.induction_on with
  | C coefficient => simp [binaryProjection]
  | add first second first_eq second_eq => simp only [map_add, first_eq, second_eq, add_zero]
  | mul_X polynomial index induction_hypothesis =>
    rw [map_mul]
    rw [pderiv_mul, induction_hypothesis, zero_mul, zero_add]
    simp only [binaryProjection, bind₁_X_right]
    fin_cases index <;> simp

theorem binaryProjection_eq_self (polynomial : Poly) (binary : pderiv 0 polynomial = 0) :
    binaryProjection polynomial = polynomial := by
  apply MvPolynomial.funext
  intro coordinates
  have coordinates_eta : coordinates = ![coordinates 0, coordinates 1, coordinates 2] := by
    funext index
    fin_cases index <;> rfl
  rw [coordinates_eta]
  change polynomialValue (binaryProjection polynomial)
      (coordinates 0) (coordinates 1) (coordinates 2) =
    polynomialValue polynomial (coordinates 0) (coordinates 1) (coordinates 2)
  rw [binaryProjection, polynomialValue_bind]
  have substituted : (fun index => polynomialValue
      ((![0, X 1, X 2] : Fin 3 → Poly) index)
        (coordinates 0) (coordinates 1) (coordinates 2)) = ![0, coordinates 1, coordinates 2] := by
    funext index
    fin_cases index <;> simp [polynomialValue]
  rw [substituted]
  exact (derivative_zero_eval_binary polynomial binary _ _ _).symm

theorem bernoulliOperator_binary (degree : ℕ) (parameter polynomial : Poly)
    (binary : pderiv 0 polynomial = 0) : bernoulliOperator degree parameter polynomial = polynomial := by
  have term_zero (iterations : ℕ) (iterations_positive : 0 < iterations) :
      ((fun value : Poly => pderiv 0 value)^[iterations]) polynomial = 0 := by
    obtain ⟨remaining, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt iterations_positive)
    rw [Function.iterate_succ_apply, binary]
    exact Function.iterate_fixed (map_zero (pderiv (0 : Fin 3))) remaining
  unfold bernoulliOperator
  rw [Finset.sum_eq_single 0]
  · simp
  · intro iterations _ iterations_nonzero
    rw [term_zero iterations (Nat.pos_of_ne_zero iterations_nonzero), mul_zero]
  · simp

theorem binaryProjection_homogeneous {degree : ℕ} {polynomial : Poly}
    (homogeneous : polynomial.IsHomogeneous degree) :
    (binaryProjection polynomial).IsHomogeneous degree := by
  apply bind_homogeneous homogeneous
  intro index
  fin_cases index
  · exact isHomogeneous_zero (Fin 3) ℂ 1
  · exact isHomogeneous_X ℂ 1
  · exact isHomogeneous_X ℂ 2

theorem radicalPair_binary_normalForm {degree : ℕ} (degree_positive : 0 < degree)
    (first second : HomogeneousPoly degree)
    (binary : pderiv 0 (X 2 * bernoulliOperator degree (X 1) first.val -
      X 1 * bernoulliOperator degree (X 2) second.val) = 0) :
    ∃ primitive : HomogeneousPoly degree,
      first = ⟨binaryProjection (bernoulliOperator degree (X 1) first.val),
          binaryProjection_homogeneous
            (bernoulliOperator_homogeneous (isHomogeneous_X ℂ 1) first.property)⟩ +
        (radicalTranslation degree 1 primitive - primitive) ∧
      second = ⟨binaryProjection (bernoulliOperator degree (X 2) second.val),
          binaryProjection_homogeneous
            (bernoulliOperator_homogeneous (isHomogeneous_X ℂ 2) second.property)⟩ +
        (radicalTranslation degree 2 primitive - primitive) := by
  let first_binary : HomogeneousPoly degree :=
    ⟨binaryProjection (bernoulliOperator degree (X 1) first.val),
      binaryProjection_homogeneous
        (bernoulliOperator_homogeneous (isHomogeneous_X ℂ 1) first.property)⟩
  let second_binary : HomogeneousPoly degree :=
    ⟨binaryProjection (bernoulliOperator degree (X 2) second.val),
      binaryProjection_homogeneous
        (bernoulliOperator_homogeneous (isHomogeneous_X ℂ 2) second.property)⟩
  have contraction_eq := binaryProjection_eq_self _ binary
  change binaryProjection (X 2 * bernoulliOperator degree (X 1) first.val -
      X 1 * bernoulliOperator degree (X 2) second.val) = _ at contraction_eq
  rw [map_sub, map_mul, map_mul] at contraction_eq
  have second_variable : binaryProjection (X 1) = (X 1 : Poly) := by simp [binaryProjection]
  have third_variable : binaryProjection (X 2) = (X 2 : Poly) := by simp [binaryProjection]
  rw [second_variable, third_variable] at contraction_eq
  change X 2 * first_binary.val - X 1 * second_binary.val =
    X 2 * bernoulliOperator degree (X 1) first.val -
      X 1 * bernoulliOperator degree (X 2) second.val at contraction_eq
  have contraction_zero : X 2 * bernoulliOperator degree (X 1) (first - first_binary).val -
      X 1 * bernoulliOperator degree (X 2) (second - second_binary).val = 0 := by
    simp only [Submodule.coe_sub]
    rw [show bernoulliOperator degree (X 1) (first.val - first_binary.val) =
        bernoulliOperator degree (X 1) first.val -
          bernoulliOperator degree (X 1) first_binary.val from
            map_sub (bernoulliLinearMap degree (X 1)) _ _,
      show bernoulliOperator degree (X 2) (second.val - second_binary.val) =
        bernoulliOperator degree (X 2) second.val -
          bernoulliOperator degree (X 2) second_binary.val from
            map_sub (bernoulliLinearMap degree (X 2)) _ _]
    change X 2 * (bernoulliOperator degree (X 1) first.val -
        bernoulliOperator degree (X 1)
          (binaryProjection (bernoulliOperator degree (X 1) first.val))) -
      X 1 * (bernoulliOperator degree (X 2) second.val -
        bernoulliOperator degree (X 2)
          (binaryProjection (bernoulliOperator degree (X 2) second.val))) = 0
    rw [bernoulliOperator_binary _ _ _ (binaryProjection_pderiv _),
      bernoulliOperator_binary _ _ _ (binaryProjection_pderiv _)]
    linear_combination -contraction_eq
  obtain ⟨primitive, first_eq, second_eq⟩ := radicalPair_zero_exists_primitive
    degree_positive (first - first_binary) (second - second_binary) contraction_zero
  refine ⟨primitive, ?_, ?_⟩
  · change first = first_binary + (radicalTranslation degree 1 primitive - primitive)
    rw [first_eq]
    abel
  · change second = second_binary + (radicalTranslation degree 2 primitive - primitive)
    rw [second_eq]
    abel

theorem rationalCoefficient_binary_fixed {degree : ℕ} (polynomial : HomogeneousPoly degree)
    (binary : pderiv 0 polynomial.val = 0) (first second : ℚ) :
    rationalCoefficientComponent degree trivialCharacter
      (Adelic.lineUnipotent first second) polynomial = polynomial := by
  apply Subtype.ext
  rw [rationalCoefficient_lineUnipotent]
  apply MvPolynomial.funext
  intro coordinates
  have coordinates_eta : coordinates = ![coordinates 0, coordinates 1, coordinates 2] := by
    funext index
    fin_cases index <;> rfl
  rw [coordinates_eta]
  change polynomialValue
    (bind₁ ![X 0 - C (first : ℂ) * X 1 - C (second : ℂ) * X 2, X 1, X 2] polynomial.val)
      (coordinates 0) (coordinates 1) (coordinates 2) =
    polynomialValue polynomial.val (coordinates 0) (coordinates 1) (coordinates 2)
  rw [polynomialValue_bind]
  have substituted : (fun index => polynomialValue
      ((![X 0 - C (first : ℂ) * X 1 - C (second : ℂ) * X 2, X 1, X 2] : Fin 3 → Poly) index)
        (coordinates 0) (coordinates 1) (coordinates 2)) =
      ![coordinates 0 - (first : ℂ) * coordinates 1 - (second : ℂ) * coordinates 2,
        coordinates 1, coordinates 2] := by
    funext index
    fin_cases index <;> simp [polynomialValue]
  rw [substituted]
  exact (derivative_zero_eval_binary polynomial.val binary _ _ _).trans
    (derivative_zero_eval_binary polynomial.val binary _ _ _).symm

theorem radicalCrossed_binary_normalForm {degree : ℕ} (degree_positive : 0 < degree)
    (crossed : ℤ → ℤ → HomogeneousPoly degree)
    (relation : ∀ first second third fourth,
      crossed (first + third) (second + fourth) =
        rationalCoefficientComponent degree trivialCharacter
          (integralRadical first second).val (crossed third fourth) + crossed first second) :
    ∃ (first_binary second_binary primitive : HomogeneousPoly degree),
      pderiv 0 first_binary.val = 0 ∧ pderiv 0 second_binary.val = 0 ∧
      ∀ first second, crossed first second = first • first_binary + second • second_binary +
        (rationalCoefficientComponent degree trivialCharacter
          (integralRadical first second).val primitive - primitive) := by
  have commuting := relation 1 0 0 1
  have commuting_reverse := relation 0 1 1 0
  simp only [add_zero, zero_add, integralRadical_val, Int.cast_one, Int.cast_zero,
    rationalCoefficient_firstRadical, rationalCoefficient_secondRadical] at commuting commuting_reverse
  have pair_relation : radicalTranslation degree 1 (crossed 0 1) - crossed 0 1 =
      radicalTranslation degree 2 (crossed 1 0) - crossed 1 0 := by
    rw [commuting] at commuting_reverse
    have rearranged := congrArg (fun value : HomogeneousPoly degree =>
      value - crossed 1 0 - crossed 0 1) commuting_reverse
    exact (by abel : _ = _).trans (rearranged.trans (by abel))
  have binary := radicalCocycle_contraction_binary degree (crossed 1 0) (crossed 0 1) pair_relation
  obtain ⟨primitive, first_eq, second_eq⟩ := radicalPair_binary_normalForm degree_positive
    (crossed 1 0) (crossed 0 1) binary
  let first_binary : HomogeneousPoly degree :=
    ⟨binaryProjection (bernoulliOperator degree (X 1) (crossed 1 0).val),
      binaryProjection_homogeneous
        (bernoulliOperator_homogeneous (isHomogeneous_X ℂ 1) (crossed 1 0).property)⟩
  let second_binary : HomogeneousPoly degree :=
    ⟨binaryProjection (bernoulliOperator degree (X 2) (crossed 0 1).val),
      binaryProjection_homogeneous
        (bernoulliOperator_homogeneous (isHomogeneous_X ℂ 2) (crossed 0 1).property)⟩
  have first_fixed (first second : ℤ) : rationalCoefficientComponent degree trivialCharacter
      (integralRadical first second).val first_binary = first_binary := by
    rw [integralRadical_val]
    exact rationalCoefficient_binary_fixed first_binary (binaryProjection_pderiv _) _ _
  have second_fixed (first second : ℤ) : rationalCoefficientComponent degree trivialCharacter
      (integralRadical first second).val second_binary = second_binary := by
    rw [integralRadical_val]
    exact rationalCoefficient_binary_fixed second_binary (binaryProjection_pderiv _) _ _
  let remainder (first second : ℤ) : HomogeneousPoly degree := crossed first second -
    (first • first_binary + second • second_binary +
      (rationalCoefficientComponent degree trivialCharacter
        (integralRadical first second).val primitive - primitive))
  have remainder_relation (first second third fourth : ℤ) :
      remainder (first + third) (second + fourth) =
        rationalCoefficientComponent degree trivialCharacter
          (integralRadical first second).val (remainder third fourth) + remainder first second := by
    simp only [remainder, relation, ← integralRadical_mul, Subgroup.coe_mul,
      map_mul, Module.End.mul_apply, map_sub, map_add, map_zsmul,
      first_fixed, second_fixed, add_zsmul]
    abel
  have first_zero : remainder 1 0 = 0 := by
    change crossed 1 0 - (1 • first_binary + 0 • second_binary +
      (rationalCoefficientComponent degree trivialCharacter (integralRadical 1 0).val primitive -
        primitive)) = 0
    simp only [one_smul, zero_smul, add_zero, integralRadical_val, Int.cast_one, Int.cast_zero,
      rationalCoefficient_firstRadical]
    exact sub_eq_zero.mpr first_eq
  have second_zero : remainder 0 1 = 0 := by
    change crossed 0 1 - (0 • first_binary + 1 • second_binary +
      (rationalCoefficientComponent degree trivialCharacter (integralRadical 0 1).val primitive -
        primitive)) = 0
    simp only [one_smul, zero_smul, zero_add, integralRadical_val, Int.cast_one, Int.cast_zero,
      rationalCoefficient_secondRadical]
    exact sub_eq_zero.mpr second_eq
  have zero := integerPairCrossed_zero
    (fun first second => rationalCoefficientComponent degree trivialCharacter
      (integralRadical first second).val) remainder remainder_relation
    (rationalCoefficient_injective degree _) (rationalCoefficient_injective degree _)
    first_zero second_zero
  refine ⟨first_binary, second_binary, primitive, binaryProjection_pderiv _,
    binaryProjection_pderiv _, ?_⟩
  intro first second
  exact sub_eq_zero.mp (zero first second)

end TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers
