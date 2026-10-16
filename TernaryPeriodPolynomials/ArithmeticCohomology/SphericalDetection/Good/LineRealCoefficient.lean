module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Good.LineArchimedeanKernel

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def standardGoodLineCoefficientSubstitution (real : ℝ × ℝ) : Poly →ₐ[ℂ] Poly :=
  aeval ![X 1, X 0, C (real.2 : ℂ) * X 0 + C (real.1 : ℂ) * X 1 + X 2]

theorem standardGoodLineCoefficientSubstitution_matrix (real : ℝ × ℝ) :
    substitute (GeneralLinearGroup.map (algebraMap ℝ ℂ) (standardGoodLineRealArgument real)).val =
      standardGoodLineCoefficientSubstitution real := by
  apply MvPolynomial.algHom_ext
  intro coordinate
  rw [substitute_X]
  change linearForm ((standardGoodLineRealArgument real).val.map (algebraMap ℝ ℂ)) coordinate = _
  rw [standardGoodLineRealArgument_val]
  fin_cases coordinate <;>
    simp [linearForm, Fin.sum_univ_three, standardGoodLineCoefficientSubstitution]

/-- The inverse real argument contributes the sign from the determinant twist. -/
theorem standardGoodLineRealCoefficient_inverse (degree : ℕ) (real : ℝ × ℝ)
    (polynomial : HomogeneousPoly degree) :
    (realCoefficientComponent degree trivialCharacter (standardGoodLineRealArgument real)⁻¹ polynomial).val =
      -standardGoodLineCoefficientSubstitution real polynomial.val := by
  rw [realCoefficientComponent_trivial, map_inv]
  let matrix := GeneralLinearGroup.map (algebraMap ℝ ℂ) (standardGoodLineRealArgument real)
  have determinant : (GeneralLinearGroup.det matrix).val = -1 := by
    change ((standardGoodLineRealArgument real).val.map (algebraMap ℝ ℂ)).det = -1
    rw [standardGoodLineRealArgument_val]
    simp [Matrix.det_fin_three]
  have twist : determinantCharacter (-1) matrix⁻¹ = -1 := by
    change ((GeneralLinearGroup.det matrix⁻¹).val) ^ (-1 : ℤ) = -1
    rw [map_inv, Units.val_inv_eq_inv_val, determinant]
    norm_num
  change determinantCharacter (-1) matrix⁻¹ • substitute matrix⁻¹⁻¹.val polynomial.val = _
  rw [inv_inv, twist, neg_one_smul]
  exact congrArg Neg.neg (congrArg (fun hom : Poly →ₐ[ℂ] Poly => hom polynomial.val)
    (standardGoodLineCoefficientSubstitution_matrix real))

theorem sourceRealTranslate_standardGoodLine {degree : ℕ} (data : InducingData degree)
    (trivial : data.chi = trivialCharacter) (source : SourceCochain degree)
    (real : ℝ × ℝ) (finite : FiniteGL) (vertices : Fin 3 → RealGL3) :
    (sourceRealTranslate data.chi source (standardGoodLineRealArgument real) finite vertices).val =
      -standardGoodLineCoefficientSubstitution real
        (source (fun index => standardGoodLineRealArgument real * vertices index) (atFinite finite)).val := by
  rw [sourceRealTranslate, trivial]
  exact standardGoodLineRealCoefficient_inverse degree real _

end TernaryPeriodPolynomials.SphericalDetection.Helpers
