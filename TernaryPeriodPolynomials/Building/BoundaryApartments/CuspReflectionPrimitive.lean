module

public import TernaryPeriodPolynomials.Building.BoundaryApartments.CuspTranslationPrimitive

@[expose] public section


open GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers

open Homogeneous Matrix MvPolynomial

theorem binarySubstitutionR_square (polynomial : Poly) :
    binarySubstitutionR (binarySubstitutionR polynomial) = polynomial := by
  have square : binarySubstitutionR.comp binarySubstitutionR = AlgHom.id ℂ Poly := by
    apply MvPolynomial.algHom_ext
    intro index
    fin_cases index <;> simp [binarySubstitutionR]
  exact AlgHom.congr_fun square polynomial

theorem upperTranslation_reflection_relation (polynomial : Poly) :
    upperTranslationPolynomial (binarySubstitutionR (upperTranslationPolynomial polynomial)) =
      binarySubstitutionR polynomial := by
  have relation : upperTranslationPolynomial.comp
      (binarySubstitutionR.comp upperTranslationPolynomial) = binarySubstitutionR := by
    apply MvPolynomial.algHom_ext
    intro index
    fin_cases index <;> simp [upperTranslationPolynomial, binarySubstitutionR]
  exact AlgHom.congr_fun relation polynomial

theorem upperTranslation_reflection_B (polynomial : Poly) :
    upperTranslationPolynomial (binarySubstitutionR (binarySubstitutionB polynomial)) =
      binarySubstitutionA (binarySubstitutionA polynomial) := by
  have relation : upperTranslationPolynomial.comp (binarySubstitutionR.comp binarySubstitutionB) =
      binarySubstitutionA.comp binarySubstitutionA := by
    apply MvPolynomial.algHom_ext
    intro index
    fin_cases index <;> simp [upperTranslationPolynomial, binarySubstitutionR,
      binarySubstitutionB, binarySubstitutionA, ← map_ofNat C] <;>
      norm_num [show (C (2 : ℂ) : Poly) = 2 by exact map_ofNat C 2,
        show (C (3 : ℂ) : Poly) = 3 by exact map_ofNat C 3] <;> ring
  exact AlgHom.congr_fun relation polynomial

theorem upperCuspCoordinate_reflection_relation {degree : ℕ}
    (degree_positive : 0 < degree) {polynomial : HomogeneousPoly degree}
    {functional : EdgeChains →ₗ[ℂ] HomogeneousPoly degree}
    (functional_property : IsPolynomialFunctional polynomial functional)
    {cocycle : cocycles rationalLevel (rationalCoefficientComponent degree trivialCharacter)}
    (realizes : RealizesPathClass functional specialPaths cocycle) :
    upperTranslationPolynomial (binarySubstitutionR
      (mixedBernoulliCoordinate cocycle upperCuspTranslation.val)) =
        -mixedBernoulliCoordinate cocycle upperCuspTranslation.val := by
  have norm := bernoulliObstruction_A_norm degree_positive functional_property realizes
  rw [mixedBernoulliCoordinate_upperCusp degree_positive functional_property realizes,
    ← bernoulliObstruction_BA_relation degree_positive functional_property realizes,
    map_neg, map_neg, upperTranslation_reflection_B]
  rw [bernoulliObstruction_BA_relation degree_positive functional_property realizes]
  linear_combination -norm

theorem binaryUpperCusp_exists_reflectionPrimitive {degree : ℕ} (degree_positive : 0 < degree)
    (polynomial : HomogeneousPoly degree) (binary : pderiv 0 polynomial.val = 0)
    (boundary : ∀ first second : ℂ, polynomialValue polynomial.val first second 0 = 0)
    (reflection : upperTranslationPolynomial (binarySubstitutionR polynomial.val) = -polynomial.val) :
    ∃ primitive : HomogeneousPoly degree, pderiv 0 primitive.val = 0 ∧
      upperTranslationPolynomial primitive.val - primitive.val = polynomial.val ∧
      binarySubstitutionR primitive.val = primitive.val := by
  obtain ⟨primitive, primitive_binary, primitive_eq⟩ :=
    binaryUpperTranslation_exists_primitive degree_positive polynomial binary boundary
  have reflected_homogeneous : (binarySubstitutionR primitive.val).IsHomogeneous degree := by
    apply bind_homogeneous primitive.property
    intro index
    fin_cases index
    · exact isHomogeneous_X ℂ 0
    · exact (isHomogeneous_X ℂ 1).neg
    · exact isHomogeneous_X ℂ 2
  have reflected_binary : pderiv 0 (binarySubstitutionR primitive.val) = 0 := by
    rw [binarySubstitutionR, pderiv_bind_commutes _ (by
      intro index
      fin_cases index <;> simp), primitive_binary, map_zero]
  let averaged : HomogeneousPoly degree :=
    ⟨C (1 / 2 : ℂ) * (primitive.val + binarySubstitutionR primitive.val),
      (primitive.property.add reflected_homogeneous).C_mul (1 / 2 : ℂ)⟩
  have reflected_eq : upperTranslationPolynomial (binarySubstitutionR primitive.val) -
      binarySubstitutionR primitive.val = polynomial.val := by
    rw [← primitive_eq] at reflection
    rw [map_sub, map_sub, upperTranslation_reflection_relation] at reflection
    linear_combination -reflection + primitive_eq
  refine ⟨averaged, ?_, ?_, ?_⟩
  · change pderiv 0 (C (1 / 2 : ℂ) *
      (primitive.val + binarySubstitutionR primitive.val)) = 0
    rw [pderiv_C_mul, map_add, primitive_binary, reflected_binary, add_zero, mul_zero]
  · change upperTranslationPolynomial (C (1 / 2 : ℂ) *
        (primitive.val + binarySubstitutionR primitive.val)) -
      C (1 / 2 : ℂ) * (primitive.val + binarySubstitutionR primitive.val) = polynomial.val
    simp only [map_mul, map_add]
    rw [show upperTranslationPolynomial (C (1 / 2 : ℂ)) = C (1 / 2 : ℂ) by
      simp [upperTranslationPolynomial]]
    have combine : C (1 / 2 : ℂ) * (upperTranslationPolynomial primitive.val +
        upperTranslationPolynomial (binarySubstitutionR primitive.val)) -
        C (1 / 2 : ℂ) * (primitive.val + binarySubstitutionR primitive.val) =
      C (1 / 2 : ℂ) * ((upperTranslationPolynomial primitive.val - primitive.val) +
        (upperTranslationPolynomial (binarySubstitutionR primitive.val) -
          binarySubstitutionR primitive.val)) := by ring
    rw [combine, primitive_eq, reflected_eq]
    have scalar : C (1 / 2 : ℂ) * (2 : Poly) = 1 := by
      rw [← map_ofNat C 2, ← map_mul]
      norm_num
    rw [show polynomial.val + polynomial.val = 2 * polynomial.val by ring,
      ← mul_assoc, scalar, one_mul]
  · change binarySubstitutionR (C (1 / 2 : ℂ) *
      (primitive.val + binarySubstitutionR primitive.val)) =
        C (1 / 2 : ℂ) * (primitive.val + binarySubstitutionR primitive.val)
    simp only [map_mul, map_add, binarySubstitutionR_square]
    rw [show binarySubstitutionR (C (1 / 2 : ℂ)) = C (1 / 2 : ℂ) by
      simp [binarySubstitutionR]]
    rw [add_comm]

theorem upperCuspCoordinate_exists_reflectionPrimitive {degree : ℕ}
    (degree_positive : 0 < degree) {polynomial : HomogeneousPoly degree}
    (solution : SymmetricSolution polynomial)
    {functional : EdgeChains →ₗ[ℂ] HomogeneousPoly degree}
    (functional_property : IsPolynomialFunctional polynomial functional)
    {cocycle : cocycles rationalLevel (rationalCoefficientComponent degree trivialCharacter)}
    (realizes : RealizesPathClass functional specialPaths cocycle) :
    ∃ primitive : HomogeneousPoly (degree + 1), pderiv 0 primitive.val = 0 ∧
      upperTranslationPolynomial primitive.val - primitive.val =
        mixedBernoulliCoordinate cocycle upperCuspTranslation.val ∧
      binarySubstitutionR primitive.val = primitive.val := by
  have line_A : arithmeticBinaryA.val ∈ Adelic.lineParabolic ℚ := by
    rw [arithmeticBinaryA_val]
    exact ⟨rfl, rfl⟩
  have line_B : arithmeticBinaryB.val ∈ Adelic.lineParabolic ℚ := by
    rw [arithmeticBinaryB_val]
    exact ⟨rfl, rfl⟩
  have line_R : arithmeticBinaryR.val ∈ Adelic.lineParabolic ℚ := by
    rw [arithmeticBinaryR_val]
    exact ⟨rfl, rfl⟩
  have coordinate := mixedBernoulliCoordinate_upperCusp degree_positive functional_property realizes
  let target : Poly := -(bernoulliObstruction polynomial +
    binarySubstitutionA (bernoulliObstruction polynomial))
  have homogeneous : target.IsHomogeneous (degree + 1) := by
    have finite_homogeneous := bernoulliFinitePrimitive_homogeneous polynomial
    have transformed_homogeneous :
        (binarySubstitutionA (bernoulliObstruction polynomial)).IsHomogeneous (degree + 1) := by
      have bernoulli_homogeneous := bernoulliObstruction_homogeneous polynomial
      have inverse : binarySubstitutionA (bernoulliObstruction polynomial) =
          C (3 : ℂ) * bernoulliFinitePrimitive polynomial -
            C (2 : ℂ) * bernoulliObstruction polynomial := by
        unfold bernoulliFinitePrimitive
        have scalar : C (3 : ℂ) * C (1 / 3 : ℂ) = (1 : Poly) := by
          rw [← map_mul]
          norm_num
        rw [← mul_assoc, scalar, one_mul, map_ofNat]
        ring
      rw [inverse]
      exact (finite_homogeneous.C_mul 3).sub (bernoulli_homogeneous.C_mul 2)
    exact ((bernoulliObstruction_homogeneous polynomial).add transformed_homogeneous).neg
  rw [coordinate]
  apply binaryUpperCusp_exists_reflectionPrimitive (by omega) ⟨target, homogeneous⟩
  · change pderiv 0 target = 0
    dsimp only [target]
    rw [← coordinate]
    exact mixedBernoulliCoordinate_binary functional_property realizes upperCuspTranslation
      (Adelic.inLine_mul line_A (Adelic.inLine_mul line_A (Adelic.inLine_mul line_B line_R)))
  · intro first second
    change polynomialValue target first second 0 = 0
    dsimp only [target]
    rw [← coordinate]
    exact bernoulliObstruction_upperTranslation_boundary degree_positive solution functional_property
      realizes first second
  · change upperTranslationPolynomial (binarySubstitutionR target) = -target
    dsimp only [target]
    rw [← coordinate]
    exact upperCuspCoordinate_reflection_relation degree_positive functional_property realizes

end TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers
