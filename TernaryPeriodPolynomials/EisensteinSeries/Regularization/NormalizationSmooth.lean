module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.UnitaryNormalization
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Tactic.FunProp

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem smooth_normPower_det (groupElement : AdelicGL) (exponent : ℂ) :
    Smooth (fun realElements : Fin 1 → RealGL3 =>
      normPower (GeneralLinearGroup.det (groupElement * atInfinity (realElements 0))) exponent) := by
  let domain : Set (Fin 1 → Matrix (Fin 3) (Fin 3) ℝ) :=
    {matrices | ∀ index, (matrices index).det ≠ 0}
  have determinant_smooth : ContDiff ℝ ⊤
      (fun matrices : Fin 1 → Matrix (Fin 3) (Fin 3) ℝ => (matrices 0).det) := by
    simp only [Matrix.det_fin_three]
    fun_prop
  have logarithm_smooth : ContDiffOn ℝ ⊤
      (fun matrices : Fin 1 → Matrix (Fin 3) (Fin 3) ℝ => Real.log (matrices 0).det)
      domain := determinant_smooth.contDiffOn.log (fun _ nonzero => nonzero 0)
  have coefficient_smooth : ContDiffOn ℝ ⊤
      (fun matrices : Fin 1 → Matrix (Fin 3) (Fin 3) ℝ =>
        normPower (GeneralLinearGroup.det groupElement) exponent *
          Complex.exp (exponent * (Real.log (matrices 0).det : ℂ))) domain := by
    exact contDiffOn_const.mul
      ((contDiffOn_const.mul (Complex.ofRealCLM.contDiff.comp_contDiffOn logarithm_smooth)).cexp)
  apply coefficient_smooth.congr
  intro matrices nonzero
  change normPower (GeneralLinearGroup.det
    (groupElement * atInfinity (invertibleMatrix (matrices 0)))) exponent = _
  rw [map_mul, normPower_mul, det_atInfinity, normPower_realAdeleUnit]
  simp only [GeneralLinearGroup.val_det_apply, invertibleMatrix, dite_eq_left (nonzero 0),
    GeneralLinearGroup.val_mkOfDetNeZero, Real.log_abs]

theorem unitaryNormalize_smooth
    {degree : ℕ} {inducingData : InducingData degree}
    {family : ℂ → AdelicGL → ℂ}
    (family_induced : ∀ parameter, IsInduced inducingData .plane parameter (family parameter))
    (parameter : ℂ) (groupElement : AdelicGL) :
    Smooth (fun realElements : Fin 1 → RealGL3 =>
      unitaryNormalize degree family parameter (groupElement * atInfinity (realElements 0))) := by
  exact (smooth_normPower_det groupElement (-((degree : ℂ) + 3) / 3)).mul
    ((family_induced (parameter - ((degree : ℂ) + 3) / 2)).1 groupElement)

theorem unitaryNormalize_smooth_cusp_lift
    {degree : ℕ} {inducingData : InducingData degree}
    {family : ℂ → AdelicGL → ℂ}
    (family_induced : ∀ parameter, IsInduced inducingData .plane parameter (family parameter))
    (parameter : ℂ) (groupElement : AdelicGL) :
    ∃ vectors : (Fin 1 → RealGL3) → inducingData.cusp.smooth,
      Smooth (fun realElements => (vectors realElements).val) ∧
        ∀ realElements binaryMatrix,
          inducingData.cusp.realize (vectors realElements) binaryMatrix =
            normPower (GeneralLinearGroup.det binaryMatrix) (-inductionExponent .plane parameter) *
              unitaryNormalize degree family parameter
                (planeLevi binaryMatrix 1 * (groupElement * atInfinity (realElements 0))) := by
  obtain ⟨vectors, vectors_smooth, realization⟩ :=
    (family_induced (parameter - ((degree : ℂ) + 3) / 2)).2.2.1 groupElement
  let normalized_vectors (realElements : Fin 1 → RealGL3) : inducingData.cusp.smooth :=
    normPower (GeneralLinearGroup.det (groupElement * atInfinity (realElements 0)))
        (-((degree : ℂ) + 3) / 3) • vectors realElements
  refine ⟨normalized_vectors, ?_, ?_⟩
  · exact (smooth_normPower_det groupElement (-((degree : ℂ) + 3) / 3)).smul vectors_smooth
  · intro realElements binaryMatrix
    rw [unitaryNormalize_binary_orbit_value]
    simp only [normalized_vectors, map_smul, Pi.smul_apply, smul_eq_mul]
    rw [realization]
    rfl

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
