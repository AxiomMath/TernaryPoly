module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Normalized.InducedVectors

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem normalizedCuspVector_parabolic_value
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (parameter : ℂ) (first second : Adeles)
    (binary : BinaryAdelicGL) (scalar : Adelesˣ) (compactMatrix : AdelicGL)
    (compact : inMaximalCompact compactMatrix) :
    normalizedCuspVector flat.1 parameter (planeUnipotent first second * planeLevi binary scalar * compactMatrix) =
      (inducingData.chi.toMonoidHom scalar *
        normPower (GeneralLinearGroup.det binary) (inductionExponent .plane parameter) *
        normPower scalar (-2 * inductionExponent .plane parameter)) •
      (⟨inducingData.cusp.π binary (inducedCuspVector (flat.1 cohomologicalPoint) compactMatrix).val,
        inducingData.cusp.smooth_stable binary _ (inducedCuspVector (flat.1 cohomologicalPoint) compactMatrix).property⟩ :
        inducingData.cusp.smooth) := by
  rw [mul_assoc, normalizedCuspVector_unipotent, planeLevi_rankOne_binary binary scalar,
    mul_assoc, normalizedCuspVector_rankOne, normalizedCuspVector_binary,
    normalizedCuspVector_flat_compact flat parameter compactMatrix compact, smul_smul]
  congr 1
  ring

theorem normalizedCuspVector_exponential
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (matrix : AdelicGL) :
    ∃ weight : ℝ, ∀ parameter : ℂ, normalizedCuspVector flat.1 parameter matrix =
      Complex.exp (parameter * (weight : ℂ)) • normalizedCuspVector flat.1 0 matrix := by
  obtain ⟨first, second, binary, scalar, compactMatrix, decomposition, compact⟩ :=
    adelic_plane_levi_decomposition matrix
  let weight : ℝ := Real.log (adeleNorm (GeneralLinearGroup.det binary) : ℝ) / 3 -
    2 * Real.log (adeleNorm scalar : ℝ) / 3
  refine ⟨weight, ?_⟩
  intro parameter
  have factorization :
      normPower (GeneralLinearGroup.det binary) (inductionExponent .plane parameter) *
        normPower scalar (-2 * inductionExponent .plane parameter) =
      Complex.exp (parameter * (weight : ℂ)) *
        (normPower (GeneralLinearGroup.det binary) (inductionExponent .plane 0) *
          normPower scalar (-2 * inductionExponent .plane 0)) := by
    simp only [normPower, ← Complex.exp_add]
    congr 1
    simp only [weight, inductionExponent]
    push_cast
    ring
  rw [decomposition, normalizedCuspVector_parabolic_value flat parameter first second binary scalar compactMatrix compact,
    normalizedCuspVector_parabolic_value flat 0 first second binary scalar compactMatrix compact, smul_smul]
  congr 1
  calc
    _ = inducingData.chi.toMonoidHom scalar *
        (normPower (GeneralLinearGroup.det binary) (inductionExponent .plane parameter) *
          normPower scalar (-2 * inductionExponent .plane parameter)) := by ring
    _ = _ := by rw [factorization]; ring

theorem normalizedCuspVector_analytic
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (matrix : AdelicGL) (parameter : ℂ) :
    AnalyticAt ℂ (fun nearby => (normalizedCuspVector flat.1 nearby matrix).val) parameter := by
  obtain ⟨weight, scaling⟩ := normalizedCuspVector_exponential flat matrix
  have equality : (fun nearby => (normalizedCuspVector flat.1 nearby matrix).val) =
      (fun nearby => Complex.exp (nearby * (weight : ℂ)) • (normalizedCuspVector flat.1 0 matrix).val) := by
    funext nearby
    exact congrArg Subtype.val (scaling nearby)
  rw [equality]
  exact ((analyticAt_id.mul analyticAt_const).cexp).smul analyticAt_const

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
