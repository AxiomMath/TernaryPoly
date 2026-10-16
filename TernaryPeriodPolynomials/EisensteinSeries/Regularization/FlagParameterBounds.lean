module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.FlatParameterScaling
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.RationalIntegralDecomposition
public import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem integral_rational_finite_integral (matrix : IntegralGL3) :
    finiteGroup (rationalGroup (integralRational matrix)) ∈
      Set.range (GeneralLinearGroup.map integralEmbedding) := by
  refine ⟨GeneralLinearGroup.map (Int.castRingHom IntegralAdeles) matrix, ?_⟩
  apply Units.ext
  apply Matrix.ext
  intro row column
  change integralEmbedding (matrix.val row column : IntegralAdeles) =
    algebraMap ℚ FiniteAdeles (matrix.val row column : ℚ)
  simp

theorem finite_integral_mul {first second : AdelicGL}
    (first_integral : finiteGroup first ∈ Set.range (GeneralLinearGroup.map integralEmbedding))
    (second_integral : finiteGroup second ∈ Set.range (GeneralLinearGroup.map integralEmbedding)) :
    finiteGroup (first * second) ∈ Set.range (GeneralLinearGroup.map integralEmbedding) := by
  obtain ⟨firstIntegral, first_spec⟩ := first_integral
  obtain ⟨secondIntegral, second_spec⟩ := second_integral
  exact ⟨firstIntegral * secondIntegral, by rw [map_mul, first_spec, second_spec, map_mul]⟩

noncomputable def planeParameterWeight (matrix : AdelicGL) : ℝ :=
  Real.log (adeleNorm (GeneralLinearGroup.det matrix) : ℝ) / 3 -
    Real.log (realPlaneHeight (realGroup matrix))

theorem eisensteinSummand_real_exponential
    {degree : ℕ} {inducingData : InducingData degree}
    {family : ℂ → AdelicGL → ℂ} (flat : IsFlatSection inducingData family)
    (matrix : AdelicGL)
    (integral : finiteGroup matrix ∈ Set.range (GeneralLinearGroup.map integralEmbedding))
    (flag : Flags .plane) :
    ∃ weight : ℝ, ∀ parameter : ℂ,
      eisensteinSummand family parameter matrix flag =
        Complex.exp ((parameter - cohomologicalPoint) * (weight : ℂ)) *
          eisensteinSummand family cohomologicalPoint matrix flag := by
  obtain ⟨representative, represents⟩ := planeFlag_integral_representative flag
  refine ⟨planeParameterWeight (rationalGroup (integralRational representative)⁻¹ * matrix), ?_⟩
  intro parameter
  rw [← represents, eisensteinSummand_of_representative (flat.1 parameter),
    eisensteinSummand_of_representative (flat.1 cohomologicalPoint)]
  apply flat_section_integral_finite_scaling flat
  apply finite_integral_mul _ integral
  simpa only [map_inv] using integral_rational_finite_integral representative⁻¹

theorem real_exponential_norm_le_endpoints (coefficient base parameter lower upper : ℂ) (weight : ℝ)
    (lower_bound : lower.re ≤ parameter.re) (upper_bound : parameter.re ≤ upper.re) :
    ‖Complex.exp ((parameter - base) * (weight : ℂ)) * coefficient‖ ≤
      ‖Complex.exp ((lower - base) * (weight : ℂ)) * coefficient‖ +
        ‖Complex.exp ((upper - base) * (weight : ℂ)) * coefficient‖ := by
  simp only [norm_mul, Complex.norm_exp, Complex.mul_re, Complex.sub_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]
  by_cases nonnegative : 0 ≤ weight
  · have bound := mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (sub_le_sub_right upper_bound base.re) nonnegative))
      (norm_nonneg coefficient)
    exact bound.trans (le_add_of_nonneg_left (by positivity))
  · have bound := mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right (sub_le_sub_right lower_bound base.re) (le_of_not_ge nonnegative)))
      (norm_nonneg coefficient)
    exact bound.trans (le_add_of_nonneg_right (by positivity))

theorem eisensteinSummand_norm_le_endpoints
    {degree : ℕ} {inducingData : InducingData degree}
    {family : ℂ → AdelicGL → ℂ} (flat : IsFlatSection inducingData family)
    (matrix : AdelicGL)
    (integral : finiteGroup matrix ∈ Set.range (GeneralLinearGroup.map integralEmbedding))
    (parameter lower upper : ℂ)
    (lower_bound : lower.re ≤ parameter.re) (upper_bound : parameter.re ≤ upper.re)
    (flag : Flags .plane) :
    ‖eisensteinSummand family parameter matrix flag‖ ≤
      ‖eisensteinSummand family lower matrix flag‖ + ‖eisensteinSummand family upper matrix flag‖ := by
  obtain ⟨weight, scaling⟩ := eisensteinSummand_real_exponential flat matrix integral flag
  rw [scaling parameter, scaling lower, scaling upper]
  exact real_exponential_norm_le_endpoints _ _ _ _ _ weight lower_bound upper_bound

theorem eisenstein_parameter_locally_uniform
    {degree : ℕ} {inducingData : InducingData degree}
    {family : ℂ → AdelicGL → ℂ} (flat : IsFlatSection inducingData family)
    (matrix : AdelicGL)
    (integral : finiteGroup matrix ∈ Set.range (GeneralLinearGroup.map integralEmbedding))
    (threshold : ℝ)
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
    exact eisensteinSummand_norm_le_endpoints flat matrix integral parameter lower upper
      (lower_minimum parameter_in) (upper_maximum parameter_in) flag

theorem eisenstein_continuation_analytic_right_integral
    {degree : ℕ} {inducingData : InducingData degree}
    {family continuation : ℂ → AdelicGL → ℂ} (flat : IsFlatSection inducingData family)
    (continuation_spec : IsEisensteinContinuation family continuation) :
    ∃ threshold : ℝ, ∀ matrix : AdelicGL,
      finiteGroup matrix ∈ Set.range (GeneralLinearGroup.map integralEmbedding) →
      AnalyticOnNhd ℂ (fun parameter => continuation parameter matrix)
        {parameter : ℂ | threshold < parameter.re} := by
  obtain ⟨threshold, convergence⟩ := continuation_spec.2
  refine ⟨threshold, ?_⟩
  intro matrix integral
  have locally_uniform := eisenstein_parameter_locally_uniform flat matrix integral threshold
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
