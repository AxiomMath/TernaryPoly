module

public import TernaryPeriodPolynomials.Building.BoundaryApartments.CuspReflectionPrimitive
public import TernaryPeriodPolynomials.Building.BoundaryApartments.Radical.Surjectivity

@[expose] public section


open GeneralEisenstein

noncomputable section


namespace TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers

open Homogeneous MvPolynomial

theorem rationalCoefficient_binaryR_square (degree : ℕ)
    (polynomial : HomogeneousPoly degree) :
    rationalCoefficientComponent degree trivialCharacter binaryR
      (rationalCoefficientComponent degree trivialCharacter binaryR polynomial) = polynomial := by
  apply Subtype.ext
  simp only [rationalCoefficient_binaryR, map_neg, neg_neg]
  exact binarySubstitutionR_square polynomial.val

theorem radicalCoordinate_reflection_surjective (degree : ℕ)
    (polynomial : HomogeneousPoly (degree + 1))
    (binary : pderiv 0 polynomial.val = 0)
    (reflection : binarySubstitutionR polynomial.val = polynomial.val) :
    ∃ first second : HomogeneousPoly degree,
      pderiv 0 first.val = 0 ∧ pderiv 0 second.val = 0 ∧
      radicalContractionMap degree (first, second) = polynomial.val ∧
      rationalCoefficientComponent degree trivialCharacter binaryR (-first) = first ∧
      rationalCoefficientComponent degree trivialCharacter binaryR second = second := by
  obtain ⟨first, second, first_binary, second_binary, coordinate⟩ :=
    radicalCoordinate_binary_surjective degree polynomial binary
  let action := rationalCoefficientComponent degree trivialCharacter binaryR
  let reflected_first := -action first
  let reflected_second := action second
  let averaged_first := (1 / 2 : ℂ) • (first + reflected_first)
  let averaged_second := (1 / 2 : ℂ) • (second + reflected_second)
  have action_square (value : HomogeneousPoly degree) : action (action value) = value :=
    rationalCoefficient_binaryR_square degree value
  have first_preserved := (binaryGenerator_preserves_binary degree first first_binary).2.2
  have second_preserved := (binaryGenerator_preserves_binary degree second second_binary).2.2
  change pderiv 0 (action first).val = 0 at first_preserved
  change pderiv 0 (action second).val = 0 at second_preserved
  have reflected_coordinate :
      radicalContractionMap degree (reflected_first, reflected_second) = polynomial.val := by
    have transformed := (radicalContractionMap_binary_generator degree first second
      first_binary second_binary).2.2
    simp only [map_neg] at transformed
    change radicalContractionMap degree (-action first, action second) = _ at transformed
    rw [← radicalContractionMap_binary degree first second first_binary second_binary,
      coordinate] at transformed
    change radicalContractionMap degree (reflected_first, reflected_second) =
      binarySubstitutionR polynomial.val at transformed
    rw [reflection] at transformed
    exact transformed
  refine ⟨averaged_first, averaged_second, ?_, ?_, ?_, ?_, ?_⟩
  · change pderiv 0 ((1 / 2 : ℂ) • (first.val + -(action first).val)) = 0
    rw [MvPolynomial.smul_eq_C_mul]
    simp only [pderiv_C_mul, map_add, map_neg]
    have sum_zero := congrArg₂ (fun left right : Poly => left + -right)
      first_binary first_preserved
    calc
      C (1 / 2 : ℂ) * (pderiv 0 first.val + -pderiv 0 (action first).val) =
          C (1 / 2 : ℂ) * (0 + -0) := congrArg (fun value : Poly => C (1 / 2 : ℂ) * value) sum_zero
      _ = 0 := by simp
  · change pderiv 0 ((1 / 2 : ℂ) • (second.val + (action second).val)) = 0
    rw [MvPolynomial.smul_eq_C_mul]
    simp only [pderiv_C_mul, map_add]
    have sum_zero := congrArg₂ (fun left right : Poly => left + right)
      second_binary second_preserved
    calc
      C (1 / 2 : ℂ) * (pderiv 0 second.val + pderiv 0 (action second).val) =
          C (1 / 2 : ℂ) * (0 + 0) := congrArg (fun value : Poly => C (1 / 2 : ℂ) * value) sum_zero
      _ = 0 := by simp
  · change radicalContractionMap degree
        ((1 / 2 : ℂ) • ((first, second) + (reflected_first, reflected_second))) = _
    rw [map_smul, map_add, coordinate, reflected_coordinate]
    simp only [MvPolynomial.smul_eq_C_mul]
    have scalar : C (1 / 2 : ℂ) * (2 : Poly) = 1 := by
      rw [← map_ofNat C 2, ← map_mul]
      norm_num
    rw [show polynomial.val + polynomial.val = 2 * polynomial.val by ring,
      ← mul_assoc, scalar, one_mul]
  · change action (-((1 / 2 : ℂ) • (first + -action first))) =
      (1 / 2 : ℂ) • (first + -action first)
    simp only [map_neg, map_smul, map_add, action_square]
    rw [← smul_neg (1 / 2 : ℂ) (action first + -first), neg_add_rev, neg_neg]
  · change action ((1 / 2 : ℂ) • (second + action second)) =
      (1 / 2 : ℂ) • (second + action second)
    simp only [map_smul, map_add, action_square]
    rw [add_comm]

end TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers
