module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Adelic.PlaneDecomposition
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.FlagParameterBounds

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem eisensteinSummand_exponential
    {degree : ℕ} {inducingData : InducingData degree}
    {family : ℂ → AdelicGL → ℂ} (flat : IsFlatSection inducingData family)
    (matrix : AdelicGL) (flag : Flags .plane) :
    ∃ weight : ℝ, ∀ parameter : ℂ, eisensteinSummand family parameter matrix flag =
      Complex.exp ((parameter - cohomologicalPoint) * (weight : ℂ)) *
        eisensteinSummand family cohomologicalPoint matrix flag :=
  flat_section_real_exponential flat (rationalGroup flag.out⁻¹ * matrix)

theorem eisensteinSummand_norm_le_endpoints_all
    {degree : ℕ} {inducingData : InducingData degree}
    {family : ℂ → AdelicGL → ℂ} (flat : IsFlatSection inducingData family)
    (matrix : AdelicGL) (parameter lower upper : ℂ)
    (lower_bound : lower.re ≤ parameter.re) (upper_bound : parameter.re ≤ upper.re)
    (flag : Flags .plane) :
    ‖eisensteinSummand family parameter matrix flag‖ ≤
      ‖eisensteinSummand family lower matrix flag‖ + ‖eisensteinSummand family upper matrix flag‖ := by
  obtain ⟨weight, scaling⟩ := eisensteinSummand_exponential flat matrix flag
  rw [scaling parameter, scaling lower, scaling upper]
  exact real_exponential_norm_le_endpoints _ _ _ _ _ weight lower_bound upper_bound

theorem flat_section_norm_eq_of_re_eq
    {degree : ℕ} {inducingData : InducingData degree}
    {family : ℂ → AdelicGL → ℂ} (flat : IsFlatSection inducingData family)
    (matrix : AdelicGL) {first second : ℂ} (same_real : first.re = second.re) :
    ‖family first matrix‖ = ‖family second matrix‖ := by
  obtain ⟨weight, scaling⟩ := flat_section_real_exponential flat matrix
  rw [scaling first, scaling second]
  simp only [norm_mul, Complex.norm_exp, Complex.mul_re, Complex.sub_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero, same_real]

theorem eisensteinSummand_norm_eq_of_re_eq
    {degree : ℕ} {inducingData : InducingData degree}
    {family : ℂ → AdelicGL → ℂ} (flat : IsFlatSection inducingData family)
    (matrix : AdelicGL) (flag : Flags .plane) {first second : ℂ}
    (same_real : first.re = second.re) :
    ‖eisensteinSummand family first matrix flag‖ = ‖eisensteinSummand family second matrix flag‖ :=
  flat_section_norm_eq_of_re_eq flat _ same_real

theorem eisenstein_parameter_locally_uniform_all
    {degree : ℕ} {inducingData : InducingData degree}
    {family : ℂ → AdelicGL → ℂ} (flat : IsFlatSection inducingData family)
    (matrix : AdelicGL) (threshold : ℝ)
    (convergence : ∀ parameter : ℂ, threshold < parameter.re →
      Summable (eisensteinSummand family parameter matrix)) :
    SummableLocallyUniformlyOn (fun flag parameter => eisensteinSummand family parameter matrix flag)
      {parameter : ℂ | threshold < parameter.re} := by
  apply SummableLocallyUniformlyOn_of_locally_bounded (isOpen_lt continuous_const Complex.continuous_re)
  intro compactSet contained compact
  rcases Set.eq_empty_or_nonempty compactSet with empty | nonempty
  · subst compactSet
    exact ⟨fun _ => 0, summable_zero, by simp⟩
  · obtain ⟨lower, lower_in, lower_minimum⟩ := compact.exists_isMinOn nonempty Complex.continuous_re.continuousOn
    obtain ⟨upper, upper_in, upper_maximum⟩ := compact.exists_isMaxOn nonempty Complex.continuous_re.continuousOn
    refine ⟨fun flag => ‖eisensteinSummand family lower matrix flag‖ +
      ‖eisensteinSummand family upper matrix flag‖,
      (convergence lower (contained lower_in)).norm.add (convergence upper (contained upper_in)).norm, ?_⟩
    intro flag parameter parameter_in
    exact eisensteinSummand_norm_le_endpoints_all flat matrix parameter lower upper
      (lower_minimum parameter_in) (upper_maximum parameter_in) flag

theorem eisenstein_continuation_analytic_right
    {degree : ℕ} {inducingData : InducingData degree}
    {family continuation : ℂ → AdelicGL → ℂ} (flat : IsFlatSection inducingData family)
    (continuation_spec : IsEisensteinContinuation family continuation) :
    ∃ threshold : ℝ, ∀ matrix : AdelicGL,
      AnalyticOnNhd ℂ (fun parameter => continuation parameter matrix)
        {parameter : ℂ | threshold < parameter.re} := by
  obtain ⟨threshold, convergence⟩ := continuation_spec.2
  refine ⟨threshold, ?_⟩
  intro matrix
  have locally_uniform := eisenstein_parameter_locally_uniform_all flat matrix threshold
    (fun parameter large => (convergence parameter large matrix).summable)
  have domain_open : IsOpen {parameter : ℂ | threshold < parameter.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have analytic : AnalyticOnNhd ℂ
      (fun parameter => ∑' flag, eisensteinSummand family parameter matrix flag)
      {parameter : ℂ | threshold < parameter.re} := by
    apply DifferentiableOn.analyticOnNhd _ domain_open
    apply locally_uniform.differentiableOn domain_open
    intro flag parameter _
    exact (flat.2.1 (rationalGroup flag.out⁻¹ * matrix) parameter).differentiableAt
  intro parameter large
  apply (analytic parameter large).congr
  filter_upwards [domain_open.eventually_mem large] with nearby nearby_large
  exact (convergence nearby nearby_large matrix).tsum_eq

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
