module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.NormalizationSmooth
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.RationalNorm

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem unitaryNormalize_eisensteinSummand (degree : ℕ) (family : ℂ → AdelicGL → ℂ)
    (parameter : ℂ) (groupElement : AdelicGL) (flag : Flags .plane) :
    eisensteinSummand (unitaryNormalize degree family) parameter groupElement flag =
      normPower (Matrix.GeneralLinearGroup.det groupElement) (-((degree : ℂ) + 3) / 3) *
        eisensteinSummand family (parameter - ((degree : ℂ) + 3) / 2) groupElement flag := by
  rw [unitaryNormalize_summand, normPower_rational, one_mul]

theorem unitaryNormalize_continuation (degree : ℕ)
    {family continuation : ℂ → AdelicGL → ℂ}
    (continuation_spec : IsEisensteinContinuation family continuation) :
    IsEisensteinContinuation (unitaryNormalize degree family)
      (unitaryNormalize degree continuation) := by
  refine ⟨unitaryNormalize_meromorphic degree continuation_spec.1, ?_⟩
  obtain ⟨threshold, convergence⟩ := continuation_spec.2
  refine ⟨threshold + (((degree : ℂ) + 3) / 2).re, ?_⟩
  intro parameter parameter_large groupElement
  have shifted_large : threshold < (parameter - ((degree : ℂ) + 3) / 2).re := by
    rw [Complex.sub_re]
    linarith
  have scaled_sum := (convergence _ shifted_large groupElement).mul_left
    (normPower (Matrix.GeneralLinearGroup.det groupElement) (-((degree : ℂ) + 3) / 3))
  have summands_equal :
      (fun flag => normPower (Matrix.GeneralLinearGroup.det groupElement) (-((degree : ℂ) + 3) / 3) *
        eisensteinSummand family (parameter - ((degree : ℂ) + 3) / 2) groupElement flag) =
      eisensteinSummand (unitaryNormalize degree family) parameter groupElement := by
    funext flag
    exact (unitaryNormalize_eisensteinSummand degree family parameter groupElement flag).symm
  rw [summands_equal] at scaled_sum
  exact scaled_sum

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
