module

public import TernaryPeriodPolynomials.Building.BoundaryApartments.Radical.Contraction

@[expose] public section


open GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers

open Matrix MvPolynomial

theorem rationalCoefficient_lineUnipotent (degree : ℕ) (first second : ℚ)
    (polynomial : HomogeneousPoly degree) :
    (rationalCoefficientComponent degree trivialCharacter
      (Adelic.lineUnipotent first second) polynomial).val =
      bind₁ ![X 0 - C (first : ℂ) * X 1 - C (second : ℂ) * X 2, X 1, X 2]
        polynomial.val := by
  let complex_matrix : GL3 := GeneralLinearGroup.map (algebraMap ℝ ℂ)
    (GeneralLinearGroup.map (algebraMap ℚ ℝ) (Adelic.lineUnipotent first second))
  have trivial_action :
      (rationalCoefficientComponent degree trivialCharacter
        (Adelic.lineUnipotent first second) polynomial).val =
          action (-1) complex_matrix polynomial.val := by
    simp [rationalCoefficientComponent, realCoefficientComponent, componentCharacter,
      trivialCharacter, realCoefficient, complex_matrix]
  have determinant : ((GeneralLinearGroup.det complex_matrix : ℂˣ) : ℂ) = 1 := by
    change complex_matrix.val.det = 1
    norm_num [complex_matrix, Adelic.lineUnipotent, Adelic.upperUnipotent,
      GeneralLinearGroup.map_apply, Matrix.det_fin_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
  have substitution : substitute (complex_matrix⁻¹).val =
      bind₁ ![X 0 - C (first : ℂ) * X 1 - C (second : ℂ) * X 2, X 1, X 2] := by
    apply MvPolynomial.algHom_ext
    intro index
    fin_cases index <;>
      simp [substitute, linearForm, complex_matrix, ← map_inv,
        Adelic.lineUnipotent, Adelic.upperUnipotent, Fin.sum_univ_three]
    ring
  rw [trivial_action, action_apply]
  change ((GeneralLinearGroup.det complex_matrix : ℂˣ) : ℂ) ^ (-1 : ℤ) •
    substitute (complex_matrix⁻¹).val polynomial.val = _
  rw [determinant, one_zpow, one_smul, substitution]

theorem rationalCoefficient_firstRadical (degree : ℕ) (polynomial : HomogeneousPoly degree) :
    rationalCoefficientComponent degree trivialCharacter
      (Adelic.lineUnipotent 1 0) polynomial = radicalTranslation degree 1 polynomial := by
  apply Subtype.ext
  rw [rationalCoefficient_lineUnipotent]
  simp [radicalTranslation]

theorem rationalCoefficient_secondRadical (degree : ℕ) (polynomial : HomogeneousPoly degree) :
    rationalCoefficientComponent degree trivialCharacter
      (Adelic.lineUnipotent 0 1) polynomial = radicalTranslation degree 2 polynomial := by
  apply Subtype.ext
  rw [rationalCoefficient_lineUnipotent]
  simp [radicalTranslation]

theorem radicalContraction_groupCoboundary (degree : ℕ) (polynomial : HomogeneousPoly degree) :
    X 2 * bernoulliOperator degree (X 1)
      ((rationalCoefficientComponent degree trivialCharacter
        (Adelic.lineUnipotent 1 0) polynomial).val - polynomial.val) -
    X 1 * bernoulliOperator degree (X 2)
      ((rationalCoefficientComponent degree trivialCharacter
        (Adelic.lineUnipotent 0 1) polynomial).val - polynomial.val) = 0 := by
  rw [rationalCoefficient_firstRadical, rationalCoefficient_secondRadical]
  exact radicalContraction_coboundary degree polynomial

end TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers
