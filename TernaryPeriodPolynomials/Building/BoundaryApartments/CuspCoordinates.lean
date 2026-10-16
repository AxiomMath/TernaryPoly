module

public import TernaryPeriodPolynomials.Building.BoundaryApartments.Mixed.CoordinateRelations
public import TernaryPeriodPolynomials.Building.BoundaryApartments.Bernoulli.Cusps

@[expose] public section


open GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers

open Homogeneous Matrix MvPolynomial

theorem binarySubstitutionA_value (polynomial : Poly) (first second third : ℂ) :
    polynomialValue (binarySubstitutionA polynomial) first second third =
      polynomialValue polynomial first (-2 * second + third) (-3 * second + third) := by
  rw [binarySubstitutionA, polynomialValue_bind]
  have coordinates : (fun index => polynomialValue
      ((![X 0, -2 * X 1 + X 2, -3 * X 1 + X 2] : Fin 3 → Poly) index)
      first second third) = ![first, -2 * second + third, -3 * second + third] := by
    funext index
    fin_cases index <;> simp [polynomialValue]
  rw [coordinates]
  rfl

theorem binarySubstitutionB_value (polynomial : Poly) (first second third : ℂ) :
    polynomialValue (binarySubstitutionB polynomial) first second third =
      polynomialValue polynomial first (-second) (-3 * second + third) := by
  rw [binarySubstitutionB, polynomialValue_bind]
  have coordinates : (fun index => polynomialValue
      ((![X 0, -X 1, -3 * X 1 + X 2] : Fin 3 → Poly) index)
      first second third) = ![first, -second, -3 * second + third] := by
    funext index
    fin_cases index <;> simp [polynomialValue]
  rw [coordinates]
  rfl

theorem bernoulliObstruction_upperCusp_all {degree : ℕ}
    (degree_positive : 0 < degree) {polynomial : HomogeneousPoly degree}
    (solution : SymmetricSolution polynomial)
    {functional : EdgeChains →ₗ[ℂ] HomogeneousPoly degree}
    (functional_property : IsPolynomialFunctional polynomial functional)
    {cocycle : cocycles rationalLevel (rationalCoefficientComponent degree trivialCharacter)}
    (realizes : RealizesPathClass functional specialPaths cocycle) (first second : ℂ) :
    polynomialValue (bernoulliObstruction polynomial) first second (3 * second) = 0 := by
  by_cases degree_even : Even degree
  · exact bernoulliObstruction_upperCusp degree_positive degree_even solution first second
  · let obstruction : HomogeneousPoly (degree + 1) :=
      ⟨bernoulliObstruction polynomial, bernoulliObstruction_homogeneous polynomial⟩
    have obstruction_even : Even (degree + 1) := Nat.even_add_one.mpr degree_even
    have norm := congrArg (fun value : Poly => polynomialValue value 0 second 0)
      (bernoulliObstruction_A_norm degree_positive functional_property realizes)
    have reflection := congrArg (fun value : Poly => polynomialValue value 0 second 0)
      (bernoulliObstruction_BA_relation degree_positive functional_property realizes)
    simp only [polynomialValue, map_add, map_zero] at norm reflection
    change polynomialValue obstruction.val 0 second 0 +
      polynomialValue (binarySubstitutionA obstruction.val) 0 second 0 +
      polynomialValue (binarySubstitutionA (binarySubstitutionA obstruction.val)) 0 second 0 = 0
      at norm
    change polynomialValue (binarySubstitutionB obstruction.val) 0 second 0 =
      polynomialValue obstruction.val 0 second 0 +
        polynomialValue (binarySubstitutionA obstruction.val) 0 second 0 at reflection
    rw [binarySubstitutionA_value, binarySubstitutionA_value, binarySubstitutionA_value] at norm
    rw [binarySubstitutionB_value, binarySubstitutionA_value] at reflection
    have second_coordinate : -2 * (-2 * second + 0) + (-3 * second + 0) = second := by ring
    have third_coordinate : -3 * (-2 * second + 0) + (-3 * second + 0) = 3 * second := by ring
    rw [second_coordinate, third_coordinate] at norm
    simp only [add_zero] at norm reflection
    have first_sign : polynomialValue obstruction.val 0 (-2 * second) (-3 * second) =
        polynomialValue obstruction.val 0 (2 * second) (3 * second) := by
      have negation := polynomialValue_neg_even obstruction obstruction_even
        0 (2 * second) (3 * second)
      simpa only [neg_zero, neg_mul] using negation
    have second_sign : polynomialValue obstruction.val 0 (-second) (-3 * second) =
        polynomialValue obstruction.val 0 second (3 * second) := by
      have negation := polynomialValue_neg_even obstruction obstruction_even 0 second (3 * second)
      simpa only [neg_zero, neg_mul] using negation
    rw [first_sign] at norm
    rw [first_sign, second_sign] at reflection
    have vanishing : polynomialValue obstruction.val 0 second (3 * second) = 0 := by
      linear_combination (norm + reflection) / 2
    rw [derivative_zero_eval_binary (bernoulliObstruction polynomial)
      (bernoulliObstruction_binary functional_property)]
    exact vanishing

theorem bernoulliObstruction_upperTranslation_boundary {degree : ℕ}
    (degree_positive : 0 < degree) {polynomial : HomogeneousPoly degree}
    (solution : SymmetricSolution polynomial)
    {functional : EdgeChains →ₗ[ℂ] HomogeneousPoly degree}
    (functional_property : IsPolynomialFunctional polynomial functional)
    {cocycle : cocycles rationalLevel (rationalCoefficientComponent degree trivialCharacter)}
    (realizes : RealizesPathClass functional specialPaths cocycle) (first second : ℂ) :
    polynomialValue (mixedBernoulliCoordinate cocycle upperCuspTranslation.val)
      first second 0 = 0 := by
  rw [mixedBernoulliCoordinate_upperCusp degree_positive functional_property realizes]
  have reflection := congrArg (fun value : Poly => polynomialValue value first second 0)
    (bernoulliObstruction_BA_relation degree_positive functional_property realizes)
  change polynomialValue (binarySubstitutionB (bernoulliObstruction polynomial))
      first second 0 = polynomialValue
        (bernoulliObstruction polynomial + binarySubstitutionA (bernoulliObstruction polynomial))
          first second 0 at reflection
  simp only [polynomialValue, map_neg]
  change -polynomialValue
    (bernoulliObstruction polynomial + binarySubstitutionA (bernoulliObstruction polynomial))
      first second 0 = 0
  rw [← reflection, binarySubstitutionB_value]
  have vanishing := bernoulliObstruction_upperCusp_all degree_positive solution functional_property
    realizes first (-second)
  simpa only [add_zero, mul_neg, neg_mul, neg_zero] using congrArg Neg.neg vanishing

end TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers
