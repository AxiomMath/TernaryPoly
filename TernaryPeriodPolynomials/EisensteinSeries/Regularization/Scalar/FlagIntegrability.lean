module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.LargeDegreeRegularization
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Radical.Continuity

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory Filter

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem eisensteinSummand_of_unitaryNormalize (degree : ℕ) (family : ℂ → AdelicGL → ℂ)
    (parameter : ℂ) (matrix : AdelicGL) (flag : Flags .plane) :
    eisensteinSummand family parameter matrix flag =
      normPower (GeneralLinearGroup.det matrix) (((degree : ℂ) + 3) / 3) *
        eisensteinSummand (unitaryNormalize degree family)
          (parameter + ((degree : ℂ) + 3) / 2) matrix flag := by
  rw [unitaryNormalize_eisensteinSummand, add_sub_cancel_right, ← mul_assoc, ← normPower_add]
  have cancel : ((degree : ℂ) + 3) / 3 + (-((degree : ℂ) + 3) / 3) = 0 := by ring
  rw [cancel, normPower_zero, one_mul]

theorem shifted_parameter_large {degree : ℕ} {parameter : ℂ}
    (large : -(degree : ℝ) / 2 < parameter.re) :
    3 / 2 < (parameter + ((degree : ℂ) + 3) / 2).re := by
  norm_num [Complex.add_re, Complex.div_re]
  linarith

theorem scalar_flag_summable
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (parameter : ℂ)
    (large : -(degree : ℝ) / 2 < parameter.re) (matrix : AdelicGL) :
    Summable (eisensteinSummand family parameter matrix) := by
  have normalized := (normalized_scalar_sum_analytic flat matrix).2 _ (shifted_parameter_large large)
  exact (normalized.mul_left (normPower (GeneralLinearGroup.det matrix) (((degree : ℂ) + 3) / 3))).congr
    (fun flag => (eisensteinSummand_of_unitaryNormalize degree family parameter matrix flag).symm)

theorem scalar_flag_compact_majorant
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (parameter : ℂ)
    (large : -(degree : ℝ) / 2 < parameter.re)
    (matrices : Set AdelicGL) (compact : IsCompact matrices) :
    ∃ majorant : Flags .plane → ℝ, Summable majorant ∧
      ∀ matrix ∈ matrices, ∀ flag, ‖eisensteinSummand family parameter matrix flag‖ ≤ majorant flag := by
  obtain ⟨majorant, summable, bounded⟩ := normalized_scalar_flag_compact_majorant flat
    (normalizedScalarProfile_compact_bound flat)
    {parameter + ((degree : ℂ) + 3) / 2} matrices isCompact_singleton compact
    (by simpa only [Set.mem_singleton_iff, forall_eq] using shifted_parameter_large large)
  have factor_continuous : Continuous
      (fun matrix : AdelicGL => normPower (GeneralLinearGroup.det matrix) (((degree : ℂ) + 3) / 3)) :=
    normPower_continuous.comp (adelicDet_continuous.prodMk continuous_const)
  obtain ⟨factor_bound, factor_bounded⟩ := compact.exists_bound_of_continuousOn factor_continuous.continuousOn
  refine ⟨fun flag => max 0 factor_bound * majorant flag,
    summable.mul_left (max 0 factor_bound), ?_⟩
  intro matrix member flag
  rw [eisensteinSummand_of_unitaryNormalize, norm_mul]
  exact (mul_le_mul_of_nonneg_right ((factor_bounded matrix member).trans (le_max_right _ _))
    (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left (bounded _ rfl matrix member flag) (le_max_left _ _))

theorem scalar_flag_norm_integrals_summable
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (parameter : ℂ)
    (large : -(degree : ℝ) / 2 < parameter.re)
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (measure : Measure X) [IsFiniteMeasure measure] {map : X → AdelicGL} (continuous : Continuous map)
    (matrices : Set AdelicGL) (compact : IsCompact matrices)
    (contained : ∀ᵐ point ∂measure, map point ∈ matrices) :
    (∀ flag : Flags .plane, Integrable
      (fun point => eisensteinSummand family parameter (map point) flag) measure) ∧
    Summable (fun flag : Flags .plane => ∫ point,
      ‖eisensteinSummand family parameter (map point) flag‖ ∂measure) := by
  obtain ⟨majorant, summable, bounded⟩ := scalar_flag_compact_majorant flat parameter large matrices compact
  have scalar_continuous (flag : Flags .plane) : Continuous
      (fun point => eisensteinSummand family parameter (map point) flag) :=
    (induced_continuous (flat.1 parameter)).comp (continuous_const.mul continuous)
  have bound_ae (flag : Flags .plane) : ∀ᵐ point ∂measure,
      ‖eisensteinSummand family parameter (map point) flag‖ ≤ majorant flag := by
    filter_upwards [contained] with point member
    exact bounded (map point) member flag
  have integrable (flag : Flags .plane) : Integrable
      (fun point => eisensteinSummand family parameter (map point) flag) measure :=
    Integrable.of_bound (scalar_continuous flag).aestronglyMeasurable _ (bound_ae flag)
  refine ⟨integrable, ?_⟩
  apply (summable.mul_left (measure.real Set.univ)).of_nonneg_of_le
    (fun _ => integral_nonneg (fun _ => norm_nonneg _))
  intro flag
  have integral_bound := integral_mono_ae (integrable flag).norm (integrable_const (majorant flag)) (bound_ae flag)
  simpa only [integral_const, smul_eq_mul] using integral_bound

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
