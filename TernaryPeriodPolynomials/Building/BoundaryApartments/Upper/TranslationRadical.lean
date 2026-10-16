module

public import TernaryPeriodPolynomials.Building.BoundaryApartments.ReflectionRadicalLift

@[expose] public section


open GeneralEisenstein

noncomputable section


namespace TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers

open Homogeneous Matrix MvPolynomial

theorem upperCuspTranslation_entries :
    upperCuspTranslation.val.val = !![1,0,0;0,1,1;0,0,1] ∧
    upperCuspTranslation.val.inv = !![1,0,0;0,1,-1;0,0,1] := by
  constructor <;>
    ext row column <;>
    fin_cases row <;> fin_cases column <;>
    norm_num [upperCuspTranslation, Subgroup.coe_mul, arithmeticBinaryA_val,
      arithmeticBinaryB_val, arithmeticBinaryR_val, binaryA, binaryB, binaryR,
      GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.vecHead, Matrix.vecTail]

theorem upperCuspTranslation_line : upperCuspTranslation.val ∈ Adelic.lineParabolic ℚ := by
  constructor <;> rw [upperCuspTranslation_entries.1] <;> rfl

theorem upperCuspTranslation_block :
    upperCuspTranslation.val.val 0 1 = 0 ∧ upperCuspTranslation.val.val 0 2 = 0 := by
  rw [upperCuspTranslation_entries.1]
  exact ⟨rfl, rfl⟩

theorem upperCuspTranslation_radical_conjugate (first second : ℤ) :
    upperCuspTranslation⁻¹ * integralRadical first second * upperCuspTranslation =
      integralRadical first (first + second) := by
  apply Subtype.ext
  apply GeneralLinearGroup.ext
  intro row column
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, GeneralLinearGroup.coe_mul,
    integralRadical_val]
  change (upperCuspTranslation.val.inv *
      (Adelic.lineUnipotent (first : ℚ) (second : ℚ)).val *
      upperCuspTranslation.val.val) row column = _
  rw [upperCuspTranslation_entries.2, upperCuspTranslation_entries.1]
  fin_cases row <;> fin_cases column <;>
    simp [Adelic.lineUnipotent, Adelic.upperUnipotent, Matrix.mul_apply,
      Fin.sum_univ_three, Int.cast_add, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

theorem rationalCoefficient_upperCuspTranslation (degree : ℕ)
    (polynomial : HomogeneousPoly degree) :
    (rationalCoefficientComponent degree trivialCharacter upperCuspTranslation.val polynomial).val =
      upperTranslationPolynomial polynomial.val := by
  let complex_matrix : GL3 := GeneralLinearGroup.map (algebraMap ℝ ℂ)
    (GeneralLinearGroup.map (algebraMap ℚ ℝ) upperCuspTranslation.val)
  have trivial_action :
      (rationalCoefficientComponent degree trivialCharacter upperCuspTranslation.val polynomial).val =
        action (-1) complex_matrix polynomial.val := by
    simp [rationalCoefficientComponent, realCoefficientComponent, componentCharacter,
      trivialCharacter, realCoefficient, complex_matrix]
  have entries : complex_matrix.val = !![1,0,0;0,1,1;0,0,1] := by
    ext row column
    change ((upperCuspTranslation.val.val row column : ℝ) : ℂ) = _
    rw [upperCuspTranslation_entries.1]
    fin_cases row <;> fin_cases column <;> norm_num
  have inverse_entries : complex_matrix.inv = !![1,0,0;0,1,-1;0,0,1] := by
    ext row column
    change ((upperCuspTranslation.val.inv row column : ℝ) : ℂ) = _
    rw [upperCuspTranslation_entries.2]
    fin_cases row <;> fin_cases column <;> norm_num
  have determinant : ((GeneralLinearGroup.det complex_matrix : ℂˣ) : ℂ) = 1 := by
    change complex_matrix.val.det = 1
    rw [entries]
    norm_num [Matrix.det_fin_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
  have substitution : substitute (complex_matrix⁻¹).val = upperTranslationPolynomial := by
    apply MvPolynomial.algHom_ext
    intro index
    rw [substitute, bind₁_X_right]
    change linearForm complex_matrix.inv index = upperTranslationPolynomial (X index)
    rw [inverse_entries]
    fin_cases index <;> simp [linearForm, upperTranslationPolynomial, Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.vecHead, Matrix.vecTail, sub_eq_add_neg]
  rw [trivial_action, action_apply]
  change ((GeneralLinearGroup.det complex_matrix : ℂˣ) : ℂ) ^ (-1 : ℤ) •
    substitute (complex_matrix⁻¹).val polynomial.val = _
  rw [determinant, one_zpow, one_smul, substitution]

theorem upperCuspTranslation_preserves_binary (degree : ℕ)
    (polynomial : HomogeneousPoly degree) (binary : pderiv 0 polynomial.val = 0) :
    pderiv 0
      (rationalCoefficientComponent degree trivialCharacter upperCuspTranslation.val polynomial).val =
        0 := by
  rw [rationalCoefficient_upperCuspTranslation, upperTranslationPolynomial,
    pderiv_bind_commutes _ (by
      intro index
      fin_cases index <;> simp), binary, map_zero]

theorem radicalContractionMap_binary_upperTranslation (degree : ℕ)
    (first second : HomogeneousPoly degree)
    (first_binary : pderiv 0 first.val = 0) (second_binary : pderiv 0 second.val = 0) :
    radicalContractionMap degree
      (rationalCoefficientComponent degree trivialCharacter upperCuspTranslation.val (first + second),
       rationalCoefficientComponent degree trivialCharacter upperCuspTranslation.val second) =
        upperTranslationPolynomial (radicalContractionMap degree (first, second)) := by
  rw [radicalContractionMap_binary degree first second first_binary second_binary,
    radicalContractionMap_binary]
  · simp only [map_add, Submodule.coe_add, rationalCoefficient_upperCuspTranslation,
      map_sub, map_mul]
    rw [show upperTranslationPolynomial (X 2 : Poly) = X 2 by
      rw [upperTranslationPolynomial, bind₁_X_right]; rfl,
      show upperTranslationPolynomial (X 1 : Poly) = X 1 - X 2 by
        rw [upperTranslationPolynomial, bind₁_X_right]; rfl]
    ring
  · apply upperCuspTranslation_preserves_binary
    change pderiv 0 (first.val + second.val) = 0
    rw [map_add, first_binary, second_binary, add_zero]
  · exact upperCuspTranslation_preserves_binary degree second second_binary

end TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers
