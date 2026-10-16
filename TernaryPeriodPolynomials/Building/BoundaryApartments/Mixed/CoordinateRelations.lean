module

public import TernaryPeriodPolynomials.Building.BoundaryApartments.Mixed.CoordinateCocycle

@[expose] public section


open GeneralEisenstein

noncomputable section


namespace TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers

open Homogeneous Matrix MvPolynomial

def binarySubstitutionA : Poly →ₐ[ℂ] Poly :=
  bind₁ ![X 0, -2 * X 1 + X 2, -3 * X 1 + X 2]

def binarySubstitutionB : Poly →ₐ[ℂ] Poly :=
  bind₁ ![X 0, -X 1, -3 * X 1 + X 2]

def binarySubstitutionR : Poly →ₐ[ℂ] Poly := bind₁ ![X 0, -X 1, X 2]

theorem arithmeticBinaryA_cube : arithmeticBinaryA ^ 3 = 1 := by
  apply Subtype.ext
  rw [Subgroup.coe_pow, Subgroup.coe_one, arithmeticBinaryA_val]
  apply GeneralLinearGroup.ext
  intro row column
  fin_cases row <;> fin_cases column <;>
    norm_num [pow_succ, binaryA, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.vecHead, Matrix.vecTail]

theorem arithmeticBinaryB_reflection :
    arithmeticBinaryB * arithmeticBinaryA * arithmeticBinaryB = arithmeticBinaryA ^ 2 := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_pow, arithmeticBinaryA_val, arithmeticBinaryB_val]
  apply GeneralLinearGroup.ext
  intro row column
  fin_cases row <;> fin_cases column <;>
    norm_num [pow_two, binaryA, binaryB, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.vecHead, Matrix.vecTail]

theorem specialPaths_one : specialPaths 1 = 0 := by
  rw [specialPaths_levi 1 (by constructor <;> simp)
    (by constructor <;> simp), Subgroup.coe_one, translateChain_one, sub_self]

theorem mixedBernoulliCoordinate_one {degree : ℕ}
    {functional : EdgeChains →ₗ[ℂ] HomogeneousPoly degree}
    {cocycle : cocycles rationalLevel (rationalCoefficientComponent degree trivialCharacter)}
    (realizes : RealizesPathClass functional specialPaths cocycle) :
    mixedBernoulliCoordinate cocycle 1 = 0 := by
  have coordinate := mixedBernoulliCoordinate_of_radicalValues realizes 1
    (by constructor <;> simp)
  simp only [Subgroup.coe_one, mixedRadicalChain, specialPaths_one, map_zero, sub_self]
    at coordinate
  change mixedBernoulliCoordinate cocycle 1 = -radicalContractionMap degree 0 at coordinate
  simpa only [map_zero, neg_zero] using coordinate

theorem mixedBernoulliCoordinate_A_norm {degree : ℕ} (degree_positive : 0 < degree)
    {polynomial : HomogeneousPoly degree}
    {functional : EdgeChains →ₗ[ℂ] HomogeneousPoly degree}
    (functional_property : IsPolynomialFunctional polynomial functional)
    {cocycle : cocycles rationalLevel (rationalCoefficientComponent degree trivialCharacter)}
    (realizes : RealizesPathClass functional specialPaths cocycle) :
    mixedBernoulliCoordinate cocycle binaryA +
      binarySubstitutionA (mixedBernoulliCoordinate cocycle binaryA) +
      binarySubstitutionA (binarySubstitutionA (mixedBernoulliCoordinate cocycle binaryA)) = 0 := by
  have line : arithmeticBinaryA.val ∈ Adelic.lineParabolic ℚ := by
    rw [arithmeticBinaryA_val]
    exact ⟨rfl, rfl⟩
  have block : arithmeticBinaryA.val.val 0 1 = 0 ∧ arithmeticBinaryA.val.val 0 2 = 0 := by
    rw [arithmeticBinaryA_val]
    exact ⟨rfl, rfl⟩
  have first := (mixedBernoulliCoordinate_generator_product degree_positive functional_property
    realizes arithmeticBinaryA line block).1
  have second := (mixedBernoulliCoordinate_generator_product degree_positive functional_property
    realizes (arithmeticBinaryA * arithmeticBinaryA) (Adelic.inLine_mul line line)
      (rationalLevi_product_block _ _ block block)).1
  have cube : arithmeticBinaryA * (arithmeticBinaryA * arithmeticBinaryA) = 1 := by
    rw [← mul_assoc, ← pow_two, ← pow_succ, arithmeticBinaryA_cube]
  rw [cube, Subgroup.coe_one, mixedBernoulliCoordinate_one realizes, first,
    arithmeticBinaryA_val] at second
  change 0 = mixedBernoulliCoordinate cocycle binaryA +
    binarySubstitutionA (mixedBernoulliCoordinate cocycle binaryA +
      binarySubstitutionA (mixedBernoulliCoordinate cocycle binaryA)) at second
  rw [map_add] at second
  exact (by abel : _ = _).trans second.symm

theorem bernoulliObstruction_A_norm {degree : ℕ} (degree_positive : 0 < degree)
    {polynomial : HomogeneousPoly degree}
    {functional : EdgeChains →ₗ[ℂ] HomogeneousPoly degree}
    (functional_property : IsPolynomialFunctional polynomial functional)
    {cocycle : cocycles rationalLevel (rationalCoefficientComponent degree trivialCharacter)}
    (realizes : RealizesPathClass functional specialPaths cocycle) :
    bernoulliObstruction polynomial + binarySubstitutionA (bernoulliObstruction polynomial) +
      binarySubstitutionA (binarySubstitutionA (bernoulliObstruction polynomial)) = 0 := by
  have relation := mixedBernoulliCoordinate_A_norm degree_positive functional_property realizes
  rw [mixedBernoulliCoordinate_binaryA functional_property realizes] at relation
  simp only [map_neg] at relation
  linear_combination -relation

theorem mixedBernoulliCoordinate_BA_relation {degree : ℕ}
    (degree_positive : 0 < degree) {polynomial : HomogeneousPoly degree}
    {functional : EdgeChains →ₗ[ℂ] HomogeneousPoly degree}
    (functional_property : IsPolynomialFunctional polynomial functional)
    {cocycle : cocycles rationalLevel (rationalCoefficientComponent degree trivialCharacter)}
    (realizes : RealizesPathClass functional specialPaths cocycle) :
    binarySubstitutionB (mixedBernoulliCoordinate cocycle binaryA) =
      mixedBernoulliCoordinate cocycle binaryA +
        binarySubstitutionA (mixedBernoulliCoordinate cocycle binaryA) := by
  have line_A : arithmeticBinaryA.val ∈ Adelic.lineParabolic ℚ := by
    rw [arithmeticBinaryA_val]
    exact ⟨rfl, rfl⟩
  have line_B : arithmeticBinaryB.val ∈ Adelic.lineParabolic ℚ := by
    rw [arithmeticBinaryB_val]
    exact ⟨rfl, rfl⟩
  have block_A : arithmeticBinaryA.val.val 0 1 = 0 ∧ arithmeticBinaryA.val.val 0 2 = 0 := by
    rw [arithmeticBinaryA_val]
    exact ⟨rfl, rfl⟩
  have block_B : arithmeticBinaryB.val.val 0 1 = 0 ∧ arithmeticBinaryB.val.val 0 2 = 0 := by
    rw [arithmeticBinaryB_val]
    exact ⟨rfl, rfl⟩
  have value_AB := (mixedBernoulliCoordinate_generator_product degree_positive functional_property
    realizes arithmeticBinaryB line_B block_B).1
  have value_BAB := (mixedBernoulliCoordinate_generator_product degree_positive functional_property
    realizes (arithmeticBinaryA * arithmeticBinaryB) (Adelic.inLine_mul line_A line_B)
      (rationalLevi_product_block _ _ block_A block_B)).2.1
  have value_AA := (mixedBernoulliCoordinate_generator_product degree_positive functional_property
    realizes arithmeticBinaryA line_A block_A).1
  have reflection : arithmeticBinaryB * (arithmeticBinaryA * arithmeticBinaryB) =
      arithmeticBinaryA * arithmeticBinaryA := by
    rw [← mul_assoc, arithmeticBinaryB_reflection, pow_two]
  rw [reflection, value_AA, value_AB, arithmeticBinaryA_val,
    arithmeticBinaryB_val, mixedBernoulliCoordinate_binaryB realizes,
    map_zero, add_zero, zero_add] at value_BAB
  exact value_BAB.symm

theorem bernoulliObstruction_BA_relation {degree : ℕ}
    (degree_positive : 0 < degree) {polynomial : HomogeneousPoly degree}
    {functional : EdgeChains →ₗ[ℂ] HomogeneousPoly degree}
    (functional_property : IsPolynomialFunctional polynomial functional)
    {cocycle : cocycles rationalLevel (rationalCoefficientComponent degree trivialCharacter)}
    (realizes : RealizesPathClass functional specialPaths cocycle) :
    binarySubstitutionB (bernoulliObstruction polynomial) =
      bernoulliObstruction polynomial + binarySubstitutionA (bernoulliObstruction polynomial) := by
  have relation := mixedBernoulliCoordinate_BA_relation degree_positive functional_property realizes
  rw [mixedBernoulliCoordinate_binaryA functional_property realizes] at relation
  simp only [map_neg] at relation
  linear_combination -relation

theorem binarySubstitutionA_cube (polynomial : Poly) :
    binarySubstitutionA (binarySubstitutionA (binarySubstitutionA polynomial)) = polynomial := by
  have cube : binarySubstitutionA.comp (binarySubstitutionA.comp binarySubstitutionA) =
      AlgHom.id ℂ Poly := by
    apply MvPolynomial.algHom_ext
    intro index
    fin_cases index <;> simp [binarySubstitutionA, ← map_ofNat C] <;>
      norm_num [show (C (2 : ℂ) : Poly) = 2 by exact map_ofNat C 2,
        show (C (3 : ℂ) : Poly) = 3 by exact map_ofNat C 3] <;> ring
  exact AlgHom.congr_fun cube polynomial

theorem binarySubstitutionB_square (polynomial : Poly) :
    binarySubstitutionB (binarySubstitutionB polynomial) = polynomial := by
  have square : binarySubstitutionB.comp binarySubstitutionB = AlgHom.id ℂ Poly := by
    apply MvPolynomial.algHom_ext
    intro index
    fin_cases index <;> simp [binarySubstitutionB, ← map_ofNat C]
  exact AlgHom.congr_fun square polynomial

theorem binarySubstitutionB_conjugate (polynomial : Poly) :
    binarySubstitutionB (binarySubstitutionA (binarySubstitutionB polynomial)) =
      binarySubstitutionA (binarySubstitutionA polynomial) := by
  have conjugate : binarySubstitutionB.comp (binarySubstitutionA.comp binarySubstitutionB) =
      binarySubstitutionA.comp binarySubstitutionA := by
    apply MvPolynomial.algHom_ext
    intro index
    fin_cases index <;> simp [binarySubstitutionA, binarySubstitutionB, ← map_ofNat C] <;>
      norm_num [show (C (2 : ℂ) : Poly) = 2 by exact map_ofNat C 2,
        show (C (3 : ℂ) : Poly) = 3 by exact map_ofNat C 3] <;> ring
  exact AlgHom.congr_fun conjugate polynomial

def bernoulliFinitePrimitive {degree : ℕ} (polynomial : HomogeneousPoly degree) : Poly :=
  C (1 / 3 : ℂ) * (2 * bernoulliObstruction polynomial +
    binarySubstitutionA (bernoulliObstruction polynomial))

theorem bernoulliFinitePrimitive_A {degree : ℕ}
    (degree_positive : 0 < degree) {polynomial : HomogeneousPoly degree}
    {functional : EdgeChains →ₗ[ℂ] HomogeneousPoly degree}
    (functional_property : IsPolynomialFunctional polynomial functional)
    {cocycle : cocycles rationalLevel (rationalCoefficientComponent degree trivialCharacter)}
    (realizes : RealizesPathClass functional specialPaths cocycle) :
    bernoulliFinitePrimitive polynomial -
      binarySubstitutionA (bernoulliFinitePrimitive polynomial) = bernoulliObstruction polynomial := by
  have norm := bernoulliObstruction_A_norm degree_positive functional_property realizes
  unfold bernoulliFinitePrimitive
  have constants : binarySubstitutionA (C (1 / 3 : ℂ)) = C (1 / 3 : ℂ) := by
    simp [binarySubstitutionA]
  have two : binarySubstitutionA (2 : Poly) = 2 := by
    change bind₁ _ (2 : Poly) = 2
    exact map_ofNat _ 2
  rw [map_mul, constants, map_add, map_mul, two]
  have third : (C (1 / 3 : ℂ) : Poly) * 3 = 1 := by
    rw [← map_ofNat C 3, ← map_mul]
    norm_num
  linear_combination -C (1 / 3 : ℂ) * norm + bernoulliObstruction polynomial * third

theorem bernoulliFinitePrimitive_B {degree : ℕ}
    (degree_positive : 0 < degree) {polynomial : HomogeneousPoly degree}
    {functional : EdgeChains →ₗ[ℂ] HomogeneousPoly degree}
    (functional_property : IsPolynomialFunctional polynomial functional)
    {cocycle : cocycles rationalLevel (rationalCoefficientComponent degree trivialCharacter)}
    (realizes : RealizesPathClass functional specialPaths cocycle) :
    binarySubstitutionB (bernoulliFinitePrimitive polynomial) = bernoulliFinitePrimitive polynomial := by
  have relation := bernoulliObstruction_BA_relation degree_positive functional_property realizes
  have norm := bernoulliObstruction_A_norm degree_positive functional_property realizes
  have conjugate := binarySubstitutionB_conjugate (binarySubstitutionB (bernoulliObstruction polynomial))
  rw [binarySubstitutionB_square, relation, map_add] at conjugate
  have cube := binarySubstitutionA_cube (bernoulliObstruction polynomial)
  rw [map_add, cube] at conjugate
  unfold bernoulliFinitePrimitive
  have constants : binarySubstitutionB (C (1 / 3 : ℂ)) = C (1 / 3 : ℂ) := by
    simp [binarySubstitutionB]
  have two : binarySubstitutionB (2 : Poly) = 2 := by
    change bind₁ _ (2 : Poly) = 2
    exact map_ofNat _ 2
  rw [map_mul, constants, map_add, map_mul, two, relation, conjugate]
  linear_combination C (1 / 3 : ℂ) * norm

theorem bernoulliFinitePrimitive_homogeneous {degree : ℕ} (polynomial : HomogeneousPoly degree) :
    (bernoulliFinitePrimitive polynomial).IsHomogeneous (degree + 1) := by
  have transformed := bind_homogeneous (bernoulliObstruction_homogeneous polynomial)
    (![X 0, -2 * X 1 + X 2, -3 * X 1 + X 2] : Fin 3 → Poly) (by
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
        simpa only [map_ofNat, neg_mul] using scaled.neg.add (isHomogeneous_X ℂ (2 : Fin 3)))
  change (C (1 / 3 : ℂ) * (2 * bernoulliObstruction polynomial +
    binarySubstitutionA (bernoulliObstruction polynomial))).IsHomogeneous (degree + 1)
  rw [← map_ofNat C 2]
  exact (((bernoulliObstruction_homogeneous polynomial).C_mul 2).add transformed).C_mul
    (1 / 3 : ℂ)

theorem bernoulliFinitePrimitive_binary {degree : ℕ}
    (degree_positive : 0 < degree) {polynomial : HomogeneousPoly degree}
    {functional : EdgeChains →ₗ[ℂ] HomogeneousPoly degree}
    (functional_property : IsPolynomialFunctional polynomial functional)
    {cocycle : cocycles rationalLevel (rationalCoefficientComponent degree trivialCharacter)}
    (realizes : RealizesPathClass functional specialPaths cocycle) :
    pderiv 0 (bernoulliFinitePrimitive polynomial) = 0 := by
  have norm := bernoulliObstruction_A_norm degree_positive functional_property realizes
  have binary := bernoulliObstruction_binary functional_property
  have transformed : pderiv 0 (binarySubstitutionA (bernoulliObstruction polynomial)) = 0 := by
    rw [binarySubstitutionA, pderiv_bind_commutes _ (by
      intro index
      fin_cases index <;> simp [← map_ofNat C]), binary, map_zero]
  have second_transformed :
      pderiv 0 (binarySubstitutionA (binarySubstitutionA (bernoulliObstruction polynomial))) = 0 := by
    have differentiated := congrArg (pderiv (0 : Fin 3)) norm
    simpa only [map_add, binary, transformed, zero_add, map_zero] using differentiated
  rw [bernoulliFinitePrimitive, show 2 * bernoulliObstruction polynomial +
      binarySubstitutionA (bernoulliObstruction polynomial) =
      bernoulliObstruction polynomial -
        binarySubstitutionA (binarySubstitutionA (bernoulliObstruction polynomial)) by
    linear_combination norm]
  simp only [pderiv_C_mul, map_sub, binary, second_transformed, sub_self, mul_zero]

def upperCuspTranslation : rationalLevel :=
  arithmeticBinaryA * (arithmeticBinaryA * (arithmeticBinaryB * arithmeticBinaryR))

def lowerCuspTranslation : rationalLevel := arithmeticBinaryB * arithmeticBinaryR

theorem mixedBernoulliCoordinate_lowerCusp {degree : ℕ}
    (degree_positive : 0 < degree) {polynomial : HomogeneousPoly degree}
    {functional : EdgeChains →ₗ[ℂ] HomogeneousPoly degree}
    (functional_property : IsPolynomialFunctional polynomial functional)
    {cocycle : cocycles rationalLevel (rationalCoefficientComponent degree trivialCharacter)}
    (realizes : RealizesPathClass functional specialPaths cocycle) :
    mixedBernoulliCoordinate cocycle lowerCuspTranslation.val = 0 := by
  have product := (mixedBernoulliCoordinate_generator_product degree_positive functional_property
    realizes arithmeticBinaryR (by rw [arithmeticBinaryR_val]; exact ⟨rfl, rfl⟩)
      (by rw [arithmeticBinaryR_val]; exact ⟨rfl, rfl⟩)).2.1
  rw [arithmeticBinaryR_val, mixedBernoulliCoordinate_binaryB realizes,
    mixedBernoulliCoordinate_binaryR realizes, map_zero, add_zero] at product
  exact product

theorem mixedBernoulliCoordinate_upperCusp {degree : ℕ}
    (degree_positive : 0 < degree) {polynomial : HomogeneousPoly degree}
    {functional : EdgeChains →ₗ[ℂ] HomogeneousPoly degree}
    (functional_property : IsPolynomialFunctional polynomial functional)
    {cocycle : cocycles rationalLevel (rationalCoefficientComponent degree trivialCharacter)}
    (realizes : RealizesPathClass functional specialPaths cocycle) :
    mixedBernoulliCoordinate cocycle upperCuspTranslation.val =
      -(bernoulliObstruction polynomial + binarySubstitutionA (bernoulliObstruction polynomial)) := by
  have line_A : arithmeticBinaryA.val ∈ Adelic.lineParabolic ℚ := by
    rw [arithmeticBinaryA_val]
    exact ⟨rfl, rfl⟩
  have block_A : arithmeticBinaryA.val.val 0 1 = 0 ∧ arithmeticBinaryA.val.val 0 2 = 0 := by
    rw [arithmeticBinaryA_val]
    exact ⟨rfl, rfl⟩
  have line_B : arithmeticBinaryB.val ∈ Adelic.lineParabolic ℚ := by
    rw [arithmeticBinaryB_val]
    exact ⟨rfl, rfl⟩
  have block_B : arithmeticBinaryB.val.val 0 1 = 0 ∧ arithmeticBinaryB.val.val 0 2 = 0 := by
    rw [arithmeticBinaryB_val]
    exact ⟨rfl, rfl⟩
  have line_R : arithmeticBinaryR.val ∈ Adelic.lineParabolic ℚ := by
    rw [arithmeticBinaryR_val]
    exact ⟨rfl, rfl⟩
  have block_R : arithmeticBinaryR.val.val 0 1 = 0 ∧ arithmeticBinaryR.val.val 0 2 = 0 := by
    rw [arithmeticBinaryR_val]
    exact ⟨rfl, rfl⟩
  have line_lower := Adelic.inLine_mul line_B line_R
  have block_lower := rationalLevi_product_block _ _ block_B block_R
  have first := (mixedBernoulliCoordinate_generator_product degree_positive functional_property
    realizes lowerCuspTranslation line_lower block_lower).1
  have second := (mixedBernoulliCoordinate_generator_product degree_positive functional_property
    realizes (arithmeticBinaryA * lowerCuspTranslation) (Adelic.inLine_mul line_A line_lower)
      (rationalLevi_product_block _ _ block_A block_lower)).1
  rw [first, mixedBernoulliCoordinate_lowerCusp degree_positive functional_property realizes,
    map_zero, add_zero, mixedBernoulliCoordinate_binaryA functional_property realizes,
    map_neg] at second
  exact second.trans (neg_add _ _).symm

end TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers
