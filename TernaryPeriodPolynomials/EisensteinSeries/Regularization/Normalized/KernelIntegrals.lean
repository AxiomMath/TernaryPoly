module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Scalar.KernelAnalyticity

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory Matrix

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem unitaryNormalize_exponential
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (matrix : AdelicGL) :
    ∃ weight : ℝ, ∀ parameter : ℂ, unitaryNormalize degree family parameter matrix =
      Complex.exp (parameter * (weight : ℂ)) • unitaryNormalize degree family 0 matrix := by
  obtain ⟨weight, scaling⟩ := normalizedCuspVector_exponential flat matrix
  refine ⟨weight, ?_⟩
  intro parameter
  have equality := congrArg (fun vector => inducingData.cusp.realize vector 1) (scaling parameter)
  simpa only [map_smul, Pi.smul_apply, normalizedCuspVector_at_one] using equality

theorem unitaryNormalize_joint_continuous
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) :
    Continuous (fun input : ℂ × AdelicGL => unitaryNormalize degree family input.1 input.2) :=
  (normPower_continuous.comp ((adelicDet_continuous.comp continuous_snd).prodMk continuous_const)).mul
    ((flat_section_joint_continuous flat).comp
      ((continuous_fst.sub continuous_const).prodMk continuous_snd))

theorem normalized_standard_integral_analytic_right
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (matrix : AdelicGL) (threshold : ℝ)
    (integrable : ∀ parameter : ℝ, threshold < parameter →
      Integrable (standardIntegrand (unitaryNormalize degree family) (parameter : ℂ) matrix) radicalMeasure) :
    AnalyticOnNhd ℂ (fun nearby => ∫ point,
      standardIntegrand (unitaryNormalize degree family) nearby matrix point ∂radicalMeasure)
      {parameter : ℂ | threshold < parameter.re} := by
  apply exponential_integral_analytic_right
    (family := fun parameter point => standardIntegrand (unitaryNormalize degree family) parameter matrix point) _
    (fun point => unitaryNormalize_exponential flat (weyl⁻¹ * lineUnipotent point.1 point.2 * matrix))
    radicalMeasure threshold integrable
  have joint := (unitaryNormalize_joint_continuous flat).comp
    (continuous_fst.prodMk
      (((continuous_const (y := weyl⁻¹)).mul lineUnipotent_continuous |>.mul
        (continuous_const (y := matrix))).comp continuous_snd))
  dsimp only [Function.comp_def] at joint
  exact joint

theorem normalized_standard_compact_integral_analytic
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (matrix : AdelicGL)
    {domain : Set (Adeles × Adeles)} (compact : IsCompact domain) (parameter : ℂ) :
    AnalyticAt ℂ (fun nearby => ∫ point in domain,
      standardIntegrand (unitaryNormalize degree family) nearby matrix point ∂radicalMeasure) parameter := by
  apply exponential_compact_integral_analytic
    (family := fun parameter point => standardIntegrand (unitaryNormalize degree family) parameter matrix point) _
    (fun point => unitaryNormalize_exponential flat (weyl⁻¹ * lineUnipotent point.1 point.2 * matrix))
    radicalMeasure compact parameter
  have joint := (unitaryNormalize_joint_continuous flat).comp
    (continuous_fst.prodMk
      (((continuous_const (y := weyl⁻¹)).mul lineUnipotent_continuous |>.mul
        (continuous_const (y := matrix))).comp continuous_snd))
  dsimp only [Function.comp_def] at joint
  exact joint

theorem normalized_standard_vector_compact_integral_analytic
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (matrix : AdelicGL)
    {domain : Set (Adeles × Adeles)} (compact : IsCompact domain) (parameter : ℂ) :
    AnalyticAt ℂ (fun nearby => ∫ point in domain,
      (normalizedCuspVector flat.1 nearby (weyl⁻¹ * lineUnipotent point.1 point.2 * matrix)).val
        ∂radicalMeasure) parameter :=
  normalizedCuspVector_compact_integral_analytic flat radicalMeasure
    ((continuous_const.mul lineUnipotent_continuous).mul continuous_const) compact parameter

theorem normalized_standard_vector_integral_analytic_right
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (matrix : AdelicGL) (threshold : ℝ)
    (integrable : ∀ parameter : ℝ, threshold < parameter →
      Integrable (fun point : Adeles × Adeles =>
        (normalizedCuspVector flat.1 (parameter : ℂ) (weyl⁻¹ * lineUnipotent point.1 point.2 * matrix)).val)
          radicalMeasure) :
    AnalyticOnNhd ℂ (fun nearby => ∫ point : Adeles × Adeles,
      (normalizedCuspVector flat.1 nearby (weyl⁻¹ * lineUnipotent point.1 point.2 * matrix)).val
        ∂radicalMeasure) {parameter : ℂ | threshold < parameter.re} := by
  apply exponential_integral_analytic_right
    (family := fun parameter (point : Adeles × Adeles) =>
      (normalizedCuspVector flat.1 parameter (weyl⁻¹ * lineUnipotent point.1 point.2 * matrix)).val)
    _ _ radicalMeasure threshold integrable
  · have joint := (normalizedCuspVector_joint_continuous flat).comp
      (continuous_fst.prodMk
        (((continuous_const (y := weyl⁻¹)).mul lineUnipotent_continuous |>.mul
          (continuous_const (y := matrix))).comp continuous_snd))
    dsimp only [Function.comp_def] at joint
    exact joint
  · intro point
    obtain ⟨weight, scaling⟩ := normalizedCuspVector_exponential flat
      (weyl⁻¹ * lineUnipotent point.1 point.2 * matrix)
    exact ⟨weight, fun parameter => congrArg Subtype.val (scaling parameter)⟩

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
