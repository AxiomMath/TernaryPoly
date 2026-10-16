module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Source.PrismCuspidal
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.TernaryCoefficientRegularity

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem standardGoodLineRealArgument_contDiff {order : WithTop ℕ∞} :
    ContDiff ℝ order (fun real : ℝ × ℝ => (standardGoodLineRealArgument real).val) := by
  simp only [standardGoodLineRealArgument_val]
  apply contDiff_pi.mpr
  intro row
  apply contDiff_pi.mpr
  intro column
  fin_cases row <;> fin_cases column <;> first | exact contDiff_const | exact contDiff_fst | exact contDiff_snd

theorem standardGoodLineRealCoefficient_functional_contDiff {degree : ℕ} {order : WithTop ℕ∞}
    (polynomial : HomogeneousPoly degree) (functional : HomogeneousPoly degree →ₗ[ℂ] ℂ) :
    ContDiff ℝ order (fun real : ℝ × ℝ => functional
      (realCoefficientComponent degree trivialCharacter (standardGoodLineRealArgument real)⁻¹ polynomial)) := by
  rw [← contDiffOn_univ]
  simp only [realCoefficientComponent_trivial]
  apply ternary_homogeneousAction_functional_contDiffOn
  · have determinant (real : ℝ × ℝ) :
        ((GeneralLinearGroup.det (GeneralLinearGroup.map (algebraMap ℝ ℂ)
          (standardGoodLineRealArgument real)⁻¹)).val)⁻¹ = -1 := by
      rw [GeneralLinearGroup.map_det, map_inv]
      rw [map_inv, Units.val_inv_eq_inv_val, inv_inv]
      change (algebraMap ℝ ℂ) (standardGoodLineRealArgument real).val.det = -1
      rw [standardGoodLineRealArgument_det]
      norm_num
    simp only [determinant]
    exact contDiffOn_const
  · intro row column
    simp only [← map_inv, inv_inv, GeneralLinearGroup.val_map_apply]
    change ContDiffOn ℝ order (fun real : ℝ × ℝ =>
      algebraMap ℝ ℂ ((standardGoodLineRealArgument real).val row column)) Set.univ
    exact (Complex.ofRealCLM.contDiff.comp
      (contDiff_pi.mp (contDiff_pi.mp standardGoodLineRealArgument_contDiff row) column)).contDiffOn

theorem standardGoodLineHilbertCoefficient_contDiff {degree : ℕ} {index P : Type} [Fintype index]
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    (cusp : CuspidalRepresentation) (basis : Module.Basis index ℂ (HomogeneousPoly degree))
    (real : P → ℝ × ℝ) (real_regular : ContDiff ℝ ⊤ real)
    (vectors : P → index → cusp.H) (vectors_regular : ContDiff ℝ ⊤ vectors) :
    ContDiff ℝ ⊤ (fun point => basisHilbertCoefficient cusp basis
      (realCoefficientComponent degree trivialCharacter (standardGoodLineRealArgument (real point))⁻¹)
      (vectors point)) := by
  apply contDiff_pi.mpr
  intro position
  simp only [basisHilbertCoefficient_apply]
  apply ContDiff.sum
  intro source _
  exact ((standardGoodLineRealCoefficient_functional_contDiff (basis source) (basis.coord position)).comp
    real_regular).smul (contDiff_pi.mp vectors_regular source)

end TernaryPeriodPolynomials.SphericalDetection.Helpers
