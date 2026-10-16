module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Normalized.Continuation

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem det_weyl {R : Type*} [CommRing R] : GeneralLinearGroup.det (weyl : Adelic.GL3 R) = 1 := by
  apply Units.ext
  simp [GeneralLinearGroup.val_det_apply, weyl, Matrix.det_fin_three]

theorem det_lineUnipotent {R : Type*} [CommRing R] (first second : R) :
    GeneralLinearGroup.det (lineUnipotent first second) = 1 := by
  apply Units.ext
  simp [GeneralLinearGroup.val_det_apply, lineUnipotent, upperUnipotent, Matrix.det_fin_three]

theorem unitaryNormalize_standardIntegrand (degree : ℕ) (family : ℂ → AdelicGL → ℂ)
    (parameter : ℂ) (groupElement : AdelicGL) (coordinates : Adeles × Adeles) :
    standardIntegrand (unitaryNormalize degree family) parameter groupElement coordinates =
      normPower (GeneralLinearGroup.det groupElement) (-((degree : ℂ) + 3) / 3) *
        standardIntegrand family (parameter - ((degree : ℂ) + 3) / 2) groupElement coordinates := by
  simp only [standardIntegrand, unitaryNormalize, map_mul, map_inv,
    det_weyl, det_lineUnipotent, inv_one, one_mul]

theorem unitaryNormalize_standard_continuation (degree : ℕ)
    {family continuation : ℂ → AdelicGL → ℂ}
    (continuation_spec : IsStandardContinuation family continuation) :
    IsStandardContinuation (unitaryNormalize degree family) (unitaryNormalize degree continuation) := by
  refine ⟨unitaryNormalize_meromorphic degree continuation_spec.1, ?_⟩
  obtain ⟨threshold, convergence⟩ := continuation_spec.2
  refine ⟨threshold + (((degree : ℂ) + 3) / 2).re, ?_⟩
  intro parameter parameter_large groupElement
  have shifted_large : threshold < (parameter - ((degree : ℂ) + 3) / 2).re := by
    rw [Complex.sub_re]
    linarith
  obtain ⟨integrable, integral_eq⟩ := convergence _ shifted_large groupElement
  have integrand_eq : standardIntegrand (unitaryNormalize degree family) parameter groupElement =
      (fun coordinates => normPower (GeneralLinearGroup.det groupElement) (-((degree : ℂ) + 3) / 3) *
        standardIntegrand family (parameter - ((degree : ℂ) + 3) / 2) groupElement coordinates) :=
    funext (unitaryNormalize_standardIntegrand degree family parameter groupElement)
  rw [integrand_eq]
  refine ⟨integrable.const_mul _, ?_⟩
  rw [integral_const_mul]
  exact congrArg (fun value =>
    normPower (GeneralLinearGroup.det groupElement) (-((degree : ℂ) + 3) / 3) * value) integral_eq

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
