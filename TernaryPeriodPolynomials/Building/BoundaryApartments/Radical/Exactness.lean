module

public import TernaryPeriodPolynomials.Building.BoundaryApartments.Antiderivative
public import Mathlib.Algebra.MvPolynomial.Division

@[expose] public section


open GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers

open MvPolynomial

theorem integerCrossed_zero {Vector : Type*} [AddCommGroup Vector] [Module ℂ Vector]
    (action : ℤ → Module.End ℂ Vector) (crossed : ℤ → Vector)
    (relation : ∀ first second,
      crossed (first + second) = action first (crossed second) + crossed first)
    (action_injective : Function.Injective (action 1))
    (generator_zero : crossed 1 = 0) : ∀ integer, crossed integer = 0 := by
  have origin_zero : crossed 0 = 0 := by
    have origin := relation 0 1
    simpa only [zero_add, generator_zero, map_zero] using origin.symm
  have negative_zero : crossed (-1) = 0 := by
    apply action_injective
    have negative := relation 1 (-1)
    simpa only [add_neg_cancel, origin_zero, generator_zero, add_zero, map_zero]
      using negative.symm
  intro integer
  induction integer using Int.induction_on with
  | zero => exact origin_zero
  | succ integer induction_hypothesis =>
    rw [relation, generator_zero, map_zero, induction_hypothesis, add_zero]
  | pred integer induction_hypothesis =>
    rw [sub_eq_add_neg, relation, negative_zero, map_zero, induction_hypothesis, add_zero]

theorem integerPairCrossed_zero {Vector : Type*} [AddCommGroup Vector] [Module ℂ Vector]
    (action : ℤ → ℤ → Module.End ℂ Vector) (crossed : ℤ → ℤ → Vector)
    (relation : ∀ first second third fourth,
      crossed (first + third) (second + fourth) =
        action first second (crossed third fourth) + crossed first second)
    (first_injective : Function.Injective (action 1 0))
    (second_injective : Function.Injective (action 0 1))
    (first_zero : crossed 1 0 = 0) (second_zero : crossed 0 1 = 0) :
    ∀ first second, crossed first second = 0 := by
  have first_axis : ∀ first, crossed first 0 = 0 := by
    apply integerCrossed_zero (fun first => action first 0) (fun first => crossed first 0)
      (fun first third => by simpa using relation first 0 third 0) first_injective first_zero
  have second_axis : ∀ second, crossed 0 second = 0 := by
    apply integerCrossed_zero (fun second => action 0 second) (fun second => crossed 0 second)
      (fun second fourth => by simpa using relation 0 second 0 fourth) second_injective second_zero
  intro first second
  have value := relation first 0 0 second
  simpa only [add_zero, zero_add, first_axis, second_axis, map_zero] using value

theorem variablePair_exact (first second : Poly)
    (relation : X 2 * first = X 1 * second) :
    ∃ quotient : Poly, first = X 1 * quotient ∧ second = X 2 * quotient := by
  have divides : (X (1 : Fin 3) : Poly) ∣ X 2 * first := by
    rw [relation]
    exact dvd_mul_right _ _
  have first_divides : (X (1 : Fin 3) : Poly) ∣ first := by
    rcases X_dvd_mul_iff.mp divides with variable_divides | first_divides
    · have impossible := X_dvd_X.mp variable_divides
      exact False.elim ((by decide : (1 : Fin 3) ≠ 2) impossible)
    · exact first_divides
  obtain ⟨quotient, first_eq⟩ := first_divides
  refine ⟨quotient, first_eq, ?_⟩
  rw [first_eq] at relation
  apply mul_left_cancel₀ (X_ne_zero (1 : Fin 3))
  calc
    X 1 * second = X 2 * (X 1 * quotient) := relation.symm
    _ = X 1 * (X 2 * quotient) := by ring

theorem radicalPair_zero_exists_primitive {degree : ℕ} (degree_positive : 0 < degree)
    (first second : HomogeneousPoly degree)
    (contraction_zero : X 2 * bernoulliOperator degree (X 1) first.val -
      X 1 * bernoulliOperator degree (X 2) second.val = 0) :
    ∃ primitive : HomogeneousPoly degree,
      radicalTranslation degree 1 primitive - primitive = first ∧
      radicalTranslation degree 2 primitive - primitive = second := by
  cases degree with
  | zero => omega
  | succ predecessor =>
    obtain ⟨quotient, first_eq, second_eq⟩ := variablePair_exact
      (bernoulliOperator (predecessor + 1) (X 1) first.val)
      (bernoulliOperator (predecessor + 1) (X 2) second.val)
      (sub_eq_zero.mp contraction_zero)
    have quotient_homogeneous : quotient.IsHomogeneous predecessor := by
      apply homogeneous_of_X_mul (index := 1)
      rw [← first_eq]
      exact bernoulliOperator_homogeneous (isHomogeneous_X ℂ 1) first.property
    let primitive : HomogeneousPoly (predecessor + 1) :=
      ⟨-polynomialAntiderivative quotient,
        (polynomialAntiderivative_homogeneous quotient_homogeneous).neg⟩
    have derivative : pderiv 0 primitive.val = -quotient := by
      change pderiv 0 (-polynomialAntiderivative quotient) = -quotient
      rw [map_neg, polynomialAntiderivative_derivative]
    refine ⟨primitive, ?_, ?_⟩
    · apply radicalBernoulli_injective (predecessor + 1) 1 (by decide)
      apply Subtype.ext
      rw [radicalBernoulli_val _ 1 (by decide), radicalBernoulli_val _ 1 (by decide)]
      change bernoulliOperator (predecessor + 1) (X 1)
        ((radicalTranslation (predecessor + 1) 1 primitive).val - primitive.val) = _
      rw [bernoulliRadical_difference _ 1 (by decide), derivative, first_eq]
      ring
    · apply radicalBernoulli_injective (predecessor + 1) 2 (by decide)
      apply Subtype.ext
      rw [radicalBernoulli_val _ 2 (by decide), radicalBernoulli_val _ 2 (by decide)]
      change bernoulliOperator (predecessor + 1) (X 2)
        ((radicalTranslation (predecessor + 1) 2 primitive).val - primitive.val) = _
      rw [bernoulliRadical_difference _ 2 (by decide), derivative, second_eq]
      ring

theorem rationalCoefficient_injective (degree : ℕ) (matrix : RationalGL3) :
    Function.Injective (rationalCoefficientComponent degree trivialCharacter matrix) := by
  apply Function.LeftInverse.injective
    (f := rationalCoefficientComponent degree trivialCharacter matrix)
    (g := rationalCoefficientComponent degree trivialCharacter matrix⁻¹)
  intro polynomial
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem radicalCrossed_zero_exists_primitive {degree : ℕ} (degree_positive : 0 < degree)
    (crossed : ℤ → ℤ → HomogeneousPoly degree)
    (relation : ∀ first second third fourth,
      crossed (first + third) (second + fourth) =
        rationalCoefficientComponent degree trivialCharacter
          (integralRadical first second).val (crossed third fourth) + crossed first second)
    (contraction_zero : X 2 * bernoulliOperator degree (X 1) (crossed 1 0).val -
      X 1 * bernoulliOperator degree (X 2) (crossed 0 1).val = 0) :
    ∃ primitive : HomogeneousPoly degree, ∀ first second,
      crossed first second = rationalCoefficientComponent degree trivialCharacter
        (integralRadical first second).val primitive - primitive := by
  obtain ⟨primitive, first_eq, second_eq⟩ := radicalPair_zero_exists_primitive
    degree_positive (crossed 1 0) (crossed 0 1) contraction_zero
  let remainder (first second : ℤ) : HomogeneousPoly degree := crossed first second -
    (rationalCoefficientComponent degree trivialCharacter
      (integralRadical first second).val primitive - primitive)
  have remainder_relation (first second third fourth : ℤ) :
      remainder (first + third) (second + fourth) =
        rationalCoefficientComponent degree trivialCharacter
          (integralRadical first second).val (remainder third fourth) + remainder first second := by
    simp only [remainder, relation, ← integralRadical_mul, Subgroup.coe_mul,
      map_mul, Module.End.mul_apply, map_sub]
    abel
  have first_zero : remainder 1 0 = 0 := by
    simp only [remainder, integralRadical_val, Int.cast_one, Int.cast_zero,
      rationalCoefficient_firstRadical, first_eq, sub_self]
  have second_zero : remainder 0 1 = 0 := by
    simp only [remainder, integralRadical_val, Int.cast_one, Int.cast_zero,
      rationalCoefficient_secondRadical, second_eq, sub_self]
  have zero := integerPairCrossed_zero
    (fun first second => rationalCoefficientComponent degree trivialCharacter
      (integralRadical first second).val) remainder remainder_relation
    (rationalCoefficient_injective degree _) (rationalCoefficient_injective degree _)
    first_zero second_zero
  refine ⟨primitive, ?_⟩
  intro first second
  exact sub_eq_zero.mp (zero first second)

end TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers
