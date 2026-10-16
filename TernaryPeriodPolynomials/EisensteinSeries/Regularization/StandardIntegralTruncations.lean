module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Normalized.KernelIntegrals
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Integral.TailBounds
public import Mathlib.Topology.Compactness.SigmaCompact

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory Filter

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

noncomputable def radicalCompactExhaustion : CompactExhaustion (Adeles × Adeles) :=
  CompactExhaustion.choice (Adeles × Adeles)

theorem standard_integral_truncations_locally_uniform_right
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (matrix : AdelicGL) (threshold : ℝ)
    (integrable : ∀ parameter : ℝ, threshold < parameter →
      Integrable (standardIntegrand family (parameter : ℂ) matrix) radicalMeasure) :
    TendstoLocallyUniformlyOn
      (fun index parameter => ∫ point in radicalCompactExhaustion index,
        standardIntegrand family parameter matrix point ∂radicalMeasure)
      (fun parameter => ∫ point, standardIntegrand family parameter matrix point ∂radicalMeasure)
      atTop {parameter : ℂ | threshold < parameter.re} := by
  apply exponential_integral_truncations_locally_uniform_right
    (family := fun parameter point => standardIntegrand family parameter matrix point) _
    (fun point => flat_section_exponential_zero flat (weyl⁻¹ * lineUnipotent point.1 point.2 * matrix))
    radicalMeasure threshold integrable radicalCompactExhaustion
    (fun index => (radicalCompactExhaustion.isCompact index).measurableSet)
    radicalCompactExhaustion.subset radicalCompactExhaustion.exists_mem
  have joint := (flat_section_joint_continuous flat).comp
    (continuous_fst.prodMk
      (((continuous_const (y := weyl⁻¹)).mul lineUnipotent_continuous |>.mul
        (continuous_const (y := matrix))).comp continuous_snd))
  dsimp only [Function.comp_def] at joint
  exact joint

theorem standard_continuation_compact_approximation
    {degree : ℕ} {inducingData : InducingData degree} {family continuation : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family)
    (continuation_spec : IsStandardContinuation family continuation) :
    (∀ matrix index parameter, AnalyticAt ℂ
      (fun nearby => ∫ point in radicalCompactExhaustion index,
        standardIntegrand family nearby matrix point ∂radicalMeasure) parameter) ∧
    ∃ threshold : ℝ, ∀ matrix : AdelicGL,
      TendstoLocallyUniformlyOn
        (fun index parameter => ∫ point in radicalCompactExhaustion index,
          standardIntegrand family parameter matrix point ∂radicalMeasure)
        (fun parameter => continuation parameter matrix) atTop
        {parameter : ℂ | threshold < parameter.re} := by
  refine ⟨fun matrix index parameter => standard_compact_integral_analytic flat matrix
    (radicalCompactExhaustion.isCompact index) parameter, ?_⟩
  obtain ⟨threshold, convergence⟩ := continuation_spec.2
  refine ⟨threshold, ?_⟩
  intro matrix
  apply (standard_integral_truncations_locally_uniform_right flat matrix threshold
    (fun parameter large => (convergence (parameter : ℂ) large matrix).1)).congr_right
  intro parameter large
  exact (convergence parameter large matrix).2.symm

theorem normalized_standard_vector_truncations_locally_uniform_right
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (matrix : AdelicGL) (threshold : ℝ)
    (integrable : ∀ parameter : ℝ, threshold < parameter →
      Integrable (fun point : Adeles × Adeles =>
        (normalizedCuspVector flat.1 (parameter : ℂ) (weyl⁻¹ * lineUnipotent point.1 point.2 * matrix)).val)
          radicalMeasure) :
    TendstoLocallyUniformlyOn
      (fun index parameter => ∫ point in radicalCompactExhaustion index,
        (normalizedCuspVector flat.1 parameter (weyl⁻¹ * lineUnipotent point.1 point.2 * matrix)).val
          ∂radicalMeasure)
      (fun parameter => ∫ point : Adeles × Adeles,
        (normalizedCuspVector flat.1 parameter (weyl⁻¹ * lineUnipotent point.1 point.2 * matrix)).val
          ∂radicalMeasure) atTop {parameter : ℂ | threshold < parameter.re} := by
  apply exponential_integral_truncations_locally_uniform_right
    (family := fun parameter (point : Adeles × Adeles) =>
      (normalizedCuspVector flat.1 parameter (weyl⁻¹ * lineUnipotent point.1 point.2 * matrix)).val)
    _ _ radicalMeasure threshold integrable radicalCompactExhaustion
    (fun index => (radicalCompactExhaustion.isCompact index).measurableSet)
    radicalCompactExhaustion.subset radicalCompactExhaustion.exists_mem
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
