module

public import TernaryPeriodPolynomials.Building.BoundaryApartments.CuspCoordinates

@[expose] public section


open GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers

open Matrix MvPolynomial

def lastProjection : Poly →ₐ[ℂ] Poly := bind₁ ![X 0, X 1, 0]

theorem lastProjection_difference_dvd (polynomial : Poly) :
    (X (2 : Fin 3) : Poly) ∣ polynomial - lastProjection polynomial := by
  induction polynomial using MvPolynomial.induction_on with
  | C coefficient => simp [lastProjection]
  | add first second first_divides second_divides =>
    rw [map_add, show first + second - (lastProjection first + lastProjection second) =
      (first - lastProjection first) + (second - lastProjection second) by ring]
    exact dvd_add first_divides second_divides
  | mul_X polynomial current induction_hypothesis =>
    have variable_divides : (X (2 : Fin 3) : Poly) ∣ X current - lastProjection (X current) := by
      fin_cases current <;> simp [lastProjection]
    rw [map_mul, show polynomial * X current - lastProjection polynomial * lastProjection (X current) =
      (polynomial - lastProjection polynomial) * X current +
        lastProjection polynomial * (X current - lastProjection (X current)) by ring]
    exact dvd_add (dvd_mul_of_dvd_left induction_hypothesis _)
      (dvd_mul_of_dvd_right variable_divides _)

theorem lastVariable_dvd_of_boundary_zero (polynomial : Poly)
    (boundary : ∀ first second : ℂ, polynomialValue polynomial first second 0 = 0) :
    (X (2 : Fin 3) : Poly) ∣ polynomial := by
  have projected_zero : lastProjection polynomial = 0 := by
    apply MvPolynomial.funext
    intro coordinates
    have eta : coordinates = ![coordinates 0, coordinates 1, coordinates 2] := by
      funext index
      fin_cases index <;> rfl
    rw [eta]
    change polynomialValue (lastProjection polynomial)
      (coordinates 0) (coordinates 1) (coordinates 2) = 0
    rw [lastProjection, polynomialValue_bind]
    have projected_coordinates : (fun index => polynomialValue
        ((![X 0, X 1, 0] : Fin 3 → Poly) index)
        (coordinates 0) (coordinates 1) (coordinates 2)) =
          ![coordinates 0, coordinates 1, 0] := by
      funext index
      fin_cases index <;> simp [polynomialValue]
    rw [projected_coordinates]
    exact boundary (coordinates 0) (coordinates 1)
  simpa only [projected_zero, sub_zero] using lastProjection_difference_dvd polynomial

theorem homogeneous_lastVariable_quotient {degree : ℕ} (degree_positive : 0 < degree)
    (polynomial : HomogeneousPoly degree)
    (binary : pderiv 0 polynomial.val = 0)
    (boundary : ∀ first second : ℂ, polynomialValue polynomial.val first second 0 = 0) :
    ∃ quotient : HomogeneousPoly (degree - 1),
      polynomial.val = X 2 * quotient.val ∧ pderiv 0 quotient.val = 0 := by
  obtain ⟨quotient, quotient_eq⟩ := lastVariable_dvd_of_boundary_zero polynomial.val boundary
  have homogeneous : quotient.IsHomogeneous (degree - 1) := by
    apply homogeneous_of_X_mul (index := 2)
    rw [← quotient_eq, Nat.sub_add_cancel degree_positive]
    exact polynomial.property
  refine ⟨⟨quotient, homogeneous⟩, quotient_eq, ?_⟩
  have differentiated := binary
  rw [quotient_eq, pderiv_mul, pderiv_X_of_ne (by decide : (2 : Fin 3) ≠ 0),
    zero_mul, zero_add] at differentiated
  exact (mul_eq_zero.mp differentiated).resolve_left (X_ne_zero (2 : Fin 3))

theorem lastRadical_exists_primitive {degree : ℕ} (degree_positive : 0 < degree)
    (polynomial : HomogeneousPoly degree)
    (boundary : ∀ first second : ℂ, polynomialValue polynomial.val first second 0 = 0) :
    ∃ primitive : HomogeneousPoly degree,
      radicalTranslation degree 2 primitive - primitive = polynomial := by
  cases degree with
  | zero => omega
  | succ predecessor =>
    have bernoulli_boundary : ∀ first second : ℂ,
        polynomialValue (bernoulliOperator (predecessor + 1) (X 2) polynomial.val)
          first second 0 = 0 := by
      intro first second
      exact bernoulliOperator_eval_zero_of_line_zero (predecessor + 1) (X 2)
        polynomial.val second 0 (fun point => boundary point second) first
    obtain ⟨quotient, quotient_eq⟩ := lastVariable_dvd_of_boundary_zero
      (bernoulliOperator (predecessor + 1) (X 2) polynomial.val) bernoulli_boundary
    have homogeneous : quotient.IsHomogeneous predecessor := by
      apply homogeneous_of_X_mul (index := 2)
      rw [← quotient_eq]
      exact bernoulliOperator_homogeneous (isHomogeneous_X ℂ 2) polynomial.property
    let primitive : HomogeneousPoly (predecessor + 1) :=
      ⟨-polynomialAntiderivative quotient, (polynomialAntiderivative_homogeneous homogeneous).neg⟩
    have derivative : pderiv 0 primitive.val = -quotient := by
      change pderiv 0 (-polynomialAntiderivative quotient) = -quotient
      rw [map_neg, polynomialAntiderivative_derivative]
    refine ⟨primitive, ?_⟩
    apply radicalBernoulli_injective (predecessor + 1) 2 (by decide)
    apply Subtype.ext
    rw [radicalBernoulli_val _ 2 (by decide), radicalBernoulli_val _ 2 (by decide)]
    change bernoulliOperator (predecessor + 1) (X 2)
      ((radicalTranslation (predecessor + 1) 2 primitive).val - primitive.val) = _
    rw [bernoulliRadical_difference _ 2 (by decide), derivative, neg_mul_neg, quotient_eq]

def swapPolynomialVariables : Poly →ₐ[ℂ] Poly := bind₁ ![X 1, X 0, X 2]

def upperTranslationPolynomial : Poly →ₐ[ℂ] Poly := bind₁ ![X 0, X 1 - X 2, X 2]

theorem swapPolynomialVariables_square (polynomial : Poly) :
    swapPolynomialVariables (swapPolynomialVariables polynomial) = polynomial := by
  have square : swapPolynomialVariables.comp swapPolynomialVariables = AlgHom.id ℂ Poly := by
    apply MvPolynomial.algHom_ext
    intro index
    fin_cases index <;> simp [swapPolynomialVariables]
  exact AlgHom.congr_fun square polynomial

theorem swapPolynomialVariables_value (polynomial : Poly) (first second third : ℂ) :
    polynomialValue (swapPolynomialVariables polynomial) first second third =
      polynomialValue polynomial second first third := by
  rw [swapPolynomialVariables, polynomialValue_bind]
  have coordinates : (fun index => polynomialValue
      ((![X 1, X 0, X 2] : Fin 3 → Poly) index) first second third) =
        ![second, first, third] := by
    funext index
    fin_cases index <;> simp [polynomialValue]
  rw [coordinates]
  rfl

theorem swapPolynomialVariables_radical (polynomial : Poly) :
    swapPolynomialVariables (bind₁ ![X 0 - X 2, X 1, X 2] polynomial) =
      upperTranslationPolynomial (swapPolynomialVariables polynomial) := by
  have commute : swapPolynomialVariables.comp (bind₁ ![X 0 - X 2, X 1, X 2]) =
      upperTranslationPolynomial.comp swapPolynomialVariables := by
    apply MvPolynomial.algHom_ext
    intro index
    fin_cases index <;> simp [swapPolynomialVariables, upperTranslationPolynomial]
  exact AlgHom.congr_fun commute polynomial

theorem binaryProjection_upperTranslation (polynomial : Poly) :
    binaryProjection (upperTranslationPolynomial polynomial) =
      upperTranslationPolynomial (binaryProjection polynomial) := by
  have commute : binaryProjection.comp upperTranslationPolynomial =
      upperTranslationPolynomial.comp binaryProjection := by
    apply MvPolynomial.algHom_ext
    intro index
    fin_cases index <;> simp [binaryProjection, upperTranslationPolynomial]
  exact AlgHom.congr_fun commute polynomial

theorem binaryUpperTranslation_exists_primitive {degree : ℕ} (degree_positive : 0 < degree)
    (polynomial : HomogeneousPoly degree) (binary : pderiv 0 polynomial.val = 0)
    (boundary : ∀ first second : ℂ, polynomialValue polynomial.val first second 0 = 0) :
    ∃ primitive : HomogeneousPoly degree, pderiv 0 primitive.val = 0 ∧
      upperTranslationPolynomial primitive.val - primitive.val = polynomial.val := by
  have swap_homogeneous (value : HomogeneousPoly degree) :
      (swapPolynomialVariables value.val).IsHomogeneous degree := by
    apply bind_homogeneous value.property
    intro index
    fin_cases index
    · exact isHomogeneous_X ℂ 1
    · exact isHomogeneous_X ℂ 0
    · exact isHomogeneous_X ℂ 2
  let swapped : HomogeneousPoly degree :=
    ⟨swapPolynomialVariables polynomial.val, swap_homogeneous polynomial⟩
  obtain ⟨primitive, primitive_eq⟩ := lastRadical_exists_primitive degree_positive swapped (by
    intro first second
    change polynomialValue (swapPolynomialVariables polynomial.val) first second 0 = 0
    rw [swapPolynomialVariables_value]
    exact boundary second first)
  let unswapped : HomogeneousPoly degree :=
    ⟨swapPolynomialVariables primitive.val, swap_homogeneous primitive⟩
  let projected : HomogeneousPoly degree :=
    ⟨binaryProjection unswapped.val, binaryProjection_homogeneous unswapped.property⟩
  refine ⟨projected, binaryProjection_pderiv unswapped.val, ?_⟩
  have equality := congrArg (fun value : HomogeneousPoly degree =>
    swapPolynomialVariables value.val) primitive_eq
  change swapPolynomialVariables
    (bind₁ ![X 0 - X 2, X 1, X 2] primitive.val - primitive.val) =
      swapPolynomialVariables (swapPolynomialVariables polynomial.val) at equality
  rw [map_sub, swapPolynomialVariables_square, swapPolynomialVariables_radical] at equality
  have projected_eq := congrArg binaryProjection equality
  rw [map_sub, binaryProjection_upperTranslation, binaryProjection_eq_self polynomial.val binary]
    at projected_eq
  exact projected_eq

theorem upperCuspCoordinate_exists_translationPrimitive {degree : ℕ}
    (degree_positive : 0 < degree) {polynomial : HomogeneousPoly degree}
    (solution : SymmetricSolution polynomial)
    {functional : EdgeChains →ₗ[ℂ] HomogeneousPoly degree}
    (functional_property : IsPolynomialFunctional polynomial functional)
    {cocycle : Homogeneous.cocycles rationalLevel
      (rationalCoefficientComponent degree trivialCharacter)}
    (realizes : RealizesPathClass functional specialPaths cocycle) :
    ∃ primitive : HomogeneousPoly (degree + 1), pderiv 0 primitive.val = 0 ∧
      upperTranslationPolynomial primitive.val - primitive.val =
        mixedBernoulliCoordinate cocycle upperCuspTranslation.val := by
  have coordinate := mixedBernoulliCoordinate_upperCusp degree_positive functional_property realizes
  have transformed_homogeneous :
      (binarySubstitutionA (bernoulliObstruction polynomial)).IsHomogeneous (degree + 1) := by
    apply bind_homogeneous (bernoulliObstruction_homogeneous polynomial)
    intro index
    fin_cases index
    · exact isHomogeneous_X ℂ 0
    · change ((-2 : Poly) * X 1 + X 2).IsHomogeneous 1
      have scaled : (C (2 : ℂ) * (X (1 : Fin 3) : Poly)).IsHomogeneous 1 :=
        (isHomogeneous_X ℂ (1 : Fin 3)).C_mul 2
      simpa only [map_ofNat, neg_mul] using scaled.neg.add (isHomogeneous_X ℂ (2 : Fin 3))
    · change ((-3 : Poly) * X 1 + X 2).IsHomogeneous 1
      have scaled : (C (3 : ℂ) * (X (1 : Fin 3) : Poly)).IsHomogeneous 1 :=
        (isHomogeneous_X ℂ (1 : Fin 3)).C_mul 3
      simpa only [map_ofNat, neg_mul] using scaled.neg.add (isHomogeneous_X ℂ (2 : Fin 3))
  have homogeneous : (mixedBernoulliCoordinate cocycle upperCuspTranslation.val).IsHomogeneous
      (degree + 1) := by
    rw [coordinate]
    exact ((bernoulliObstruction_homogeneous polynomial).add transformed_homogeneous).neg
  apply binaryUpperTranslation_exists_primitive (by omega)
    ⟨mixedBernoulliCoordinate cocycle upperCuspTranslation.val, homogeneous⟩
  · exact mixedBernoulliCoordinate_binary functional_property realizes upperCuspTranslation
      (Adelic.inLine_mul (by rw [arithmeticBinaryA_val]; exact ⟨rfl, rfl⟩)
        (Adelic.inLine_mul (by rw [arithmeticBinaryA_val]; exact ⟨rfl, rfl⟩)
          (Adelic.inLine_mul (by rw [arithmeticBinaryB_val]; exact ⟨rfl, rfl⟩)
            (by rw [arithmeticBinaryR_val]; exact ⟨rfl, rfl⟩))))
  · exact bernoulliObstruction_upperTranslation_boundary degree_positive solution functional_property realizes

end TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers
