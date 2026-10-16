module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BadLine.Innerness.PolynomialBoundary
public import TernaryPeriodPolynomials.ArithmeticCohomology.BadLine.Innerness.IntegralNormalization

@[expose] public section


open GeneralEisenstein Matrix MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBadLineInnerness.Helpers

theorem rationalCoefficient_trivial_coe {n : ℕ} (g : RationalGL3)
    (f : HomogeneousPoly n) :
    (rationalCoefficientComponent n trivialCharacter g f).val =
      action (-1) (GeneralLinearGroup.map (algebraMap ℝ ℂ)
        (GeneralLinearGroup.map (algebraMap ℚ ℝ) g)) f.val := by
  change (componentCharacter trivialCharacter (GeneralLinearGroup.map (algebraMap ℚ ℝ) g) •
    realCoefficient n (GeneralLinearGroup.map (algebraMap ℚ ℝ) g) f).val = _
  simp only [componentCharacter, trivialCharacter, MonoidHom.comp_apply,
    MonoidHom.one_apply, one_smul]
  rfl

theorem rationalCoefficient_lineUnipotent {n : ℕ} (f : HomogeneousPoly n) (s t : ℚ) :
    (rationalCoefficientComponent n trivialCharacter (Adelic.lineUnipotent s t) f).val =
      evalTriple f (X 0 - C (s : ℂ)*X 1 - C (t : ℂ)*X 2) (X 1) (X 2) := by
  rw [rationalCoefficient_trivial_coe]
  have matrix_eq : GeneralLinearGroup.map (algebraMap ℝ ℂ)
      (GeneralLinearGroup.map (algebraMap ℚ ℝ) (Adelic.lineUnipotent s t)) =
        Adelic.lineUnipotent (s : ℂ) (t : ℂ) := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [GeneralLinearGroup.map_apply, Adelic.lineUnipotent, Adelic.upperUnipotent]
  rw [matrix_eq, action_apply]
  have determinant_eq : determinantCharacter (-1)
      (Adelic.lineUnipotent (s : ℂ) (t : ℂ)) = 1 := by
    simp [determinantCharacter, GeneralLinearGroup.det,
      Adelic.lineUnipotent, Adelic.upperUnipotent, Matrix.det_fin_three]
  rw [determinant_eq, one_smul]
  have linear_forms : linearForm (Adelic.lineUnipotent (s : ℂ) (t : ℂ))⁻¹.val =
      ![X 0 - C (s : ℂ)*X 1 - C (t : ℂ)*X 2, X 1, X 2] := by
    funext i
    fin_cases i <;>
      simp [linearForm, Adelic.lineUnipotent, Adelic.upperUnipotent, Fin.sum_univ_three]
    ring
  simp only [substitute, linear_forms, evalTriple, aeval_eq_bind₁]

end TernaryPeriodPolynomials.PolynomialBadLineInnerness.Helpers
