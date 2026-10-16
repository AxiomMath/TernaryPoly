module

public import TernaryPeriodPolynomials.Building.BoundaryApartments.LinePrimitiveNormalForm

@[expose] public section


open GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers

open Homogeneous Matrix MvPolynomial

def badBinaryA : badLineSubgroup :=
  ⟨arithmeticBinaryA.val, arithmeticBinaryA.property,
    by rw [arithmeticBinaryA_val]; exact ⟨rfl, rfl⟩⟩

def badBinaryB : badLineSubgroup :=
  ⟨arithmeticBinaryB.val, arithmeticBinaryB.property,
    by rw [arithmeticBinaryB_val]; exact ⟨rfl, rfl⟩⟩

def badBinaryR : badLineSubgroup :=
  ⟨arithmeticBinaryR.val, arithmeticBinaryR.property,
    by rw [arithmeticBinaryR_val]; exact ⟨rfl, rfl⟩⟩

theorem badBinaryA_val : badBinaryA.val = binaryA := arithmeticBinaryA_val
theorem badBinaryB_val : badBinaryB.val = binaryB := arithmeticBinaryB_val
theorem badBinaryR_val : badBinaryR.val = binaryR := arithmeticBinaryR_val

theorem badBinaryA_conjugate (first second : ℤ) :
    badBinaryA⁻¹ * badRadical first second * badBinaryA =
      badRadical (first + 3 * second) (-first - 2 * second) := by
  apply Subtype.ext
  apply GeneralLinearGroup.ext
  intro row column
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, badBinaryA_val, badRadical_val]
  fin_cases row <;> fin_cases column <;>
    simp [binaryA, Adelic.lineUnipotent, Adelic.upperUnipotent,
      Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem badBinaryB_conjugate (first second : ℤ) :
    badBinaryB⁻¹ * badRadical first second * badBinaryB =
      badRadical (-first - 3 * second) second := by
  apply Subtype.ext
  apply GeneralLinearGroup.ext
  intro row column
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, badBinaryB_val, badRadical_val]
  fin_cases row <;> fin_cases column <;>
    simp [binaryB, Adelic.lineUnipotent, Adelic.upperUnipotent,
      Matrix.mul_apply, Fin.sum_univ_three]
  ring

theorem badBinaryR_conjugate (first second : ℤ) :
    badBinaryR⁻¹ * badRadical first second * badBinaryR = badRadical (-first) second := by
  apply Subtype.ext
  apply GeneralLinearGroup.ext
  intro row column
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, badBinaryR_val, badRadical_val]
  fin_cases row <;> fin_cases column <;>
    simp [binaryR, Adelic.lineUnipotent, Adelic.upperUnipotent,
      Matrix.mul_apply, Fin.sum_univ_three]

theorem rationalCoefficient_binaryA (degree : ℕ) (polynomial : HomogeneousPoly degree) :
    (rationalCoefficientComponent degree trivialCharacter binaryA polynomial).val =
      bind₁ ![X 0, -2 * X 1 + X 2, -3 * X 1 + X 2] polynomial.val := by
  let complex_matrix : GL3 := GeneralLinearGroup.map (algebraMap ℝ ℂ)
    (GeneralLinearGroup.map (algebraMap ℚ ℝ) binaryA)
  have trivial_action :
      (rationalCoefficientComponent degree trivialCharacter binaryA polynomial).val =
        action (-1) complex_matrix polynomial.val := by
    simp [rationalCoefficientComponent, realCoefficientComponent, componentCharacter,
      trivialCharacter, realCoefficient, complex_matrix]
  have determinant : ((GeneralLinearGroup.det complex_matrix : ℂˣ) : ℂ) = 1 := by
    change complex_matrix.val.det = 1
    norm_num [complex_matrix, binaryA, GeneralLinearGroup.map_apply, Matrix.det_fin_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
  have substitution : substitute (complex_matrix⁻¹).val =
      bind₁ ![X 0, -2 * X 1 + X 2, -3 * X 1 + X 2] := by
    apply MvPolynomial.algHom_ext
    intro index
    fin_cases index <;>
      simp [substitute, linearForm, complex_matrix, ← map_inv, binaryA,
        Fin.sum_univ_three] <;> exact map_ofNat C _
  rw [trivial_action, action_apply]
  change ((GeneralLinearGroup.det complex_matrix : ℂˣ) : ℂ) ^ (-1 : ℤ) •
    substitute (complex_matrix⁻¹).val polynomial.val = _
  rw [determinant, one_zpow, one_smul, substitution]

theorem rationalCoefficient_binaryB (degree : ℕ) (polynomial : HomogeneousPoly degree) :
    (rationalCoefficientComponent degree trivialCharacter binaryB polynomial).val =
      -bind₁ ![X 0, -X 1, -3 * X 1 + X 2] polynomial.val := by
  let complex_matrix : GL3 := GeneralLinearGroup.map (algebraMap ℝ ℂ)
    (GeneralLinearGroup.map (algebraMap ℚ ℝ) binaryB)
  have trivial_action :
      (rationalCoefficientComponent degree trivialCharacter binaryB polynomial).val =
        action (-1) complex_matrix polynomial.val := by
    simp [rationalCoefficientComponent, realCoefficientComponent, componentCharacter,
      trivialCharacter, realCoefficient, complex_matrix]
  have determinant : ((GeneralLinearGroup.det complex_matrix : ℂˣ) : ℂ) = -1 := by
    change complex_matrix.val.det = -1
    norm_num [complex_matrix, binaryB, GeneralLinearGroup.map_apply, Matrix.det_fin_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
  have substitution : substitute (complex_matrix⁻¹).val =
      bind₁ ![X 0, -X 1, -3 * X 1 + X 2] := by
    apply MvPolynomial.algHom_ext
    intro index
    fin_cases index <;>
      simp [substitute, linearForm, complex_matrix, ← map_inv, binaryB,
        Fin.sum_univ_three]
    exact map_ofNat C _
  rw [trivial_action, action_apply]
  change ((GeneralLinearGroup.det complex_matrix : ℂˣ) : ℂ) ^ (-1 : ℤ) •
    substitute (complex_matrix⁻¹).val polynomial.val = _
  rw [determinant, substitution]
  norm_num

theorem rationalCoefficient_binaryR (degree : ℕ) (polynomial : HomogeneousPoly degree) :
    (rationalCoefficientComponent degree trivialCharacter binaryR polynomial).val =
      -bind₁ ![X 0, -X 1, X 2] polynomial.val := by
  let complex_matrix : GL3 := GeneralLinearGroup.map (algebraMap ℝ ℂ)
    (GeneralLinearGroup.map (algebraMap ℚ ℝ) binaryR)
  have trivial_action :
      (rationalCoefficientComponent degree trivialCharacter binaryR polynomial).val =
        action (-1) complex_matrix polynomial.val := by
    simp [rationalCoefficientComponent, realCoefficientComponent, componentCharacter,
      trivialCharacter, realCoefficient, complex_matrix]
  have determinant : ((GeneralLinearGroup.det complex_matrix : ℂˣ) : ℂ) = -1 := by
    change complex_matrix.val.det = -1
    norm_num [complex_matrix, binaryR, GeneralLinearGroup.map_apply, Matrix.det_fin_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
  have substitution : substitute (complex_matrix⁻¹).val = bind₁ ![X 0, -X 1, X 2] := by
    apply MvPolynomial.algHom_ext
    intro index
    fin_cases index <;>
      simp [substitute, linearForm, complex_matrix, ← map_inv, binaryR, Fin.sum_univ_three]
  rw [trivial_action, action_apply]
  change ((GeneralLinearGroup.det complex_matrix : ℂˣ) : ℂ) ^ (-1 : ℤ) •
    substitute (complex_matrix⁻¹).val polynomial.val = _
  rw [determinant, substitution]
  norm_num

end TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers
