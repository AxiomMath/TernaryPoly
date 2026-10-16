module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Scalar.ConstantTerms
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.StandardNormalization

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem normalized_scalar_sum_eq_scale (degree : ℕ) (family : ℂ → AdelicGL → ℂ)
    (parameter : ℂ) (matrix : AdelicGL) :
    (∑' flag, eisensteinSummand (unitaryNormalize degree family) parameter matrix flag) =
      normPower (GeneralLinearGroup.det matrix) (-((degree : ℂ) + 3) / 3) *
        ∑' flag, eisensteinSummand family (parameter - ((degree : ℂ) + 3) / 2) matrix flag := by
  simp_rw [unitaryNormalize_eisensteinSummand]
  rw [tsum_mul_left]

theorem normalized_scalar_plane_constant_term
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (parameter : ℂ)
    (large : 3 / 2 < parameter.re) (matrix : AdelicGL) :
    Integrable (fun point : Adeles × Adeles => ∑' flag,
      eisensteinSummand (unitaryNormalize degree family) parameter (planeUnipotent point.1 point.2 * matrix) flag)
        planeDomainMeasure ∧
    (∫ point : Adeles × Adeles, ∑' flag,
      eisensteinSummand (unitaryNormalize degree family) parameter (planeUnipotent point.1 point.2 * matrix) flag
        ∂planeDomainMeasure) = unitaryNormalize degree family parameter matrix := by
  have shifted_large : -(degree : ℝ) / 2 < (parameter - ((degree : ℂ) + 3) / 2).re := by
    norm_num
    linarith
  obtain ⟨integrable, integral_eq⟩ := scalar_plane_constant_term flat _ shifted_large matrix
  have identity : (fun point : Adeles × Adeles => ∑' flag,
      eisensteinSummand (unitaryNormalize degree family) parameter (planeUnipotent point.1 point.2 * matrix) flag) =
      (fun point => normPower (GeneralLinearGroup.det matrix) (-((degree : ℂ) + 3) / 3) *
        ∑' flag, eisensteinSummand family (parameter - ((degree : ℂ) + 3) / 2)
          (planeUnipotent point.1 point.2 * matrix) flag) := by
    funext point
    rw [normalized_scalar_sum_eq_scale, map_mul, det_planeUnipotent, one_mul]
  rw [identity]
  refine ⟨integrable.const_mul _, ?_⟩
  rw [integral_const_mul, integral_eq]
  rfl

theorem normalized_scalar_associate_constant_term
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (parameter : ℂ)
    (large : 3 / 2 < parameter.re) (matrix : AdelicGL) :
    Integrable (fun point : Adeles × Adeles => ∑' flag,
      eisensteinSummand (unitaryNormalize degree family) parameter (lineUnipotent point.1 point.2 * matrix) flag)
        planeDomainMeasure ∧
    (∫ point : Adeles × Adeles, ∑' flag,
      eisensteinSummand (unitaryNormalize degree family) parameter (lineUnipotent point.1 point.2 * matrix) flag
        ∂planeDomainMeasure) =
      ∫ point, standardIntegrand (unitaryNormalize degree family) parameter matrix point ∂radicalMeasure := by
  have shifted_large : -(degree : ℝ) / 2 < (parameter - ((degree : ℂ) + 3) / 2).re := by
    norm_num
    linarith
  obtain ⟨integrable, integral_eq⟩ := scalar_associate_constant_term flat _ shifted_large matrix
  have identity : (fun point : Adeles × Adeles => ∑' flag,
      eisensteinSummand (unitaryNormalize degree family) parameter (lineUnipotent point.1 point.2 * matrix) flag) =
      (fun point => normPower (GeneralLinearGroup.det matrix) (-((degree : ℂ) + 3) / 3) *
        ∑' flag, eisensteinSummand family (parameter - ((degree : ℂ) + 3) / 2)
          (lineUnipotent point.1 point.2 * matrix) flag) := by
    funext point
    rw [normalized_scalar_sum_eq_scale, map_mul, det_lineUnipotent, one_mul]
  rw [identity]
  refine ⟨integrable.const_mul _, ?_⟩
  rw [integral_const_mul, integral_eq]
  simp_rw [unitaryNormalize_standardIntegrand]
  rw [integral_const_mul]

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
