module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.ExponentialIntegrals
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Radical.Continuity
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.StandardNormalization

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem flat_section_exponential_zero
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (matrix : AdelicGL) :
    ∃ weight : ℝ, ∀ parameter : ℂ, family parameter matrix =
      Complex.exp (parameter * (weight : ℂ)) • family 0 matrix := by
  obtain ⟨weight, scaling⟩ := flat_section_real_exponential flat matrix
  refine ⟨weight, ?_⟩
  intro parameter
  rw [scaling parameter, scaling 0, smul_eq_mul, ← mul_assoc, ← Complex.exp_add]
  congr 2
  ring

theorem flat_section_integral_analytic_right
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family)
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (measure : Measure X) {map : X → AdelicGL} (continuous : Continuous map)
    (threshold : ℝ)
    (integrable : ∀ parameter : ℝ, threshold < parameter →
      Integrable (fun point => family (parameter : ℂ) (map point)) measure) :
    AnalyticOnNhd ℂ (fun nearby => ∫ point, family nearby (map point) ∂measure)
      {parameter : ℂ | threshold < parameter.re} := by
  apply exponential_integral_analytic_right
    (family := fun parameter point => family parameter (map point)) _
    (fun point => flat_section_exponential_zero flat (map point)) measure threshold integrable
  exact (flat_section_joint_continuous flat).comp
    (continuous_fst.prodMk (continuous.comp continuous_snd))

theorem flat_section_compact_integral_analytic
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family)
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] [T2Space X]
    (measure : Measure X) [IsFiniteMeasureOnCompacts measure]
    {map : X → AdelicGL} (continuous : Continuous map)
    {domain : Set X} (compact : IsCompact domain) (parameter : ℂ) :
    AnalyticAt ℂ (fun nearby => ∫ point in domain, family nearby (map point) ∂measure) parameter := by
  apply exponential_compact_integral_analytic
    (family := fun parameter point => family parameter (map point)) _
    (fun point => flat_section_exponential_zero flat (map point)) measure compact parameter
  exact (flat_section_joint_continuous flat).comp
    (continuous_fst.prodMk (continuous.comp continuous_snd))

theorem standard_integral_analytic_right
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (matrix : AdelicGL) (threshold : ℝ)
    (integrable : ∀ parameter : ℝ, threshold < parameter →
      Integrable (standardIntegrand family (parameter : ℂ) matrix) radicalMeasure) :
    AnalyticOnNhd ℂ (fun nearby => ∫ point, standardIntegrand family nearby matrix point ∂radicalMeasure)
      {parameter : ℂ | threshold < parameter.re} :=
  flat_section_integral_analytic_right flat radicalMeasure
    ((continuous_const.mul lineUnipotent_continuous).mul continuous_const) threshold integrable

theorem standard_compact_integral_analytic
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (matrix : AdelicGL)
    {domain : Set (Adeles × Adeles)} (compact : IsCompact domain) (parameter : ℂ) :
    AnalyticAt ℂ (fun nearby => ∫ point in domain,
      standardIntegrand family nearby matrix point ∂radicalMeasure) parameter :=
  flat_section_compact_integral_analytic flat radicalMeasure
    ((continuous_const.mul lineUnipotent_continuous).mul continuous_const) compact parameter

theorem standard_continuation_analytic_right
    {degree : ℕ} {inducingData : InducingData degree} {family continuation : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (continuation_spec : IsStandardContinuation family continuation) :
    ∃ threshold : ℝ, ∀ matrix : AdelicGL,
      AnalyticOnNhd ℂ (fun parameter => continuation parameter matrix)
        {parameter : ℂ | threshold < parameter.re} := by
  obtain ⟨threshold, convergence⟩ := continuation_spec.2
  refine ⟨threshold, ?_⟩
  intro matrix
  apply AnalyticOnNhd.congr (isOpen_lt continuous_const Complex.continuous_re)
    (standard_integral_analytic_right flat matrix threshold
      (fun parameter large => (convergence (parameter : ℂ) large matrix).1))
  intro parameter large
  exact (convergence parameter large matrix).2.symm

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
