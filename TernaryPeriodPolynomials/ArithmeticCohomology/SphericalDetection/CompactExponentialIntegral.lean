module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.WeightedExponentialIntegral

@[expose] public section


open MeasureTheory Filter

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem compactExponentialIntegral_differentiableAt
    {X E : Type} [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (measure : Measure X) [IsFiniteMeasure measure]
    (height : X → ℝ) (value : X → E)
    (height_continuous : Continuous height) (value_continuous : Continuous value)
    (parameter : ℂ) :
    DifferentiableAt ℂ (fun parameter =>
      ∫ point, Complex.exp (parameter * (height point : ℂ)) • value point ∂measure) parameter := by
  let integrand (parameter : ℂ) (point : X) := Complex.exp (parameter * (height point : ℂ)) • value point
  have integrand_continuous (parameter : ℂ) : Continuous (integrand parameter) := by
    exact (Complex.continuous_exp.comp (continuous_const.mul
      (Complex.continuous_ofReal.comp height_continuous))).smul value_continuous
  let majorant (point : X) := |height point| *
    (Real.exp ((parameter.re + 1) * height point) + Real.exp ((parameter.re - 1) * height point)) * ‖value point‖
  have majorant_continuous : Continuous majorant := by
    exact (height_continuous.abs.mul
      ((Real.continuous_exp.comp (continuous_const.mul height_continuous)).add
        (Real.continuous_exp.comp (continuous_const.mul height_continuous)))).mul value_continuous.norm
  have derivative := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := measure) (x₀ := parameter) (s := Metric.ball parameter 1)
    (F := integrand) (F' := fun parameter point => (height point : ℂ) • integrand parameter point)
    (bound := majorant) (Metric.ball_mem_nhds parameter (by norm_num))
    (Eventually.of_forall (fun other => (integrand_continuous other).aestronglyMeasurable))
    ((integrand_continuous parameter).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (((Complex.continuous_ofReal.comp height_continuous).smul
      (integrand_continuous parameter)).aestronglyMeasurable)
    (Eventually.of_forall (fun point other near => ?_))
    (majorant_continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (Eventually.of_forall (fun point other _ => ?_))
  · exact derivative.2.differentiableAt
  · have distance : |other.re - parameter.re| ≤ 1 := by
      have estimate := Complex.abs_re_le_norm (other - parameter)
      rw [Complex.sub_re] at estimate
      exact estimate.trans (le_of_lt (by simpa only [Metric.mem_ball, dist_eq_norm] using near))
    have exponential_bound := realExp_strip_bound parameter.re 1 other.re (height point) distance
    simp only [integrand, norm_smul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    exact (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right exponential_bound (norm_nonneg (value point)))
      (abs_nonneg (height point))).trans_eq (mul_assoc _ _ _).symm
  · simpa only [integrand, id_eq, one_mul, mul_one, smul_smul, mul_comm] using
      (((hasDerivAt_id other).mul_const (height point : ℂ)).cexp.smul_const (value point))

theorem compactExponentialIntegral_analyticAt
    {X E : Type} [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (measure : Measure X) [IsFiniteMeasure measure]
    (height : X → ℝ) (value : X → E)
    (height_continuous : Continuous height) (value_continuous : Continuous value)
    (parameter : ℂ) :
    AnalyticAt ℂ (fun parameter =>
      ∫ point, Complex.exp (parameter * (height point : ℂ)) • value point ∂measure) parameter := by
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  exact Eventually.of_forall (compactExponentialIntegral_differentiableAt measure height value
    height_continuous value_continuous)

theorem compactSetExponentialIntegral_analyticAt
    {X E : Type} [TopologicalSpace X] [SecondCountableTopology X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (measure : Measure X) [IsFiniteMeasureOnCompacts measure]
    (height : X → ℝ) (value : X → E)
    (height_continuous : Continuous height) (value_continuous : Continuous value)
    (domain : Set X) (compact : IsCompact domain) (parameter : ℂ) :
    AnalyticAt ℂ (fun parameter =>
      ∫ point in domain, Complex.exp (parameter * (height point : ℂ)) • value point ∂measure) parameter := by
  let : CompactSpace domain := isCompact_iff_compactSpace.mp compact
  let : IsFiniteMeasure (measure.restrict domain) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact compact.measure_lt_top⟩
  let subtypeMeasure : Measure domain := Measure.comap Subtype.val (measure.restrict domain)
  have analytic := compactExponentialIntegral_analyticAt subtypeMeasure
    (fun point : domain => height point.val) (fun point : domain => value point.val)
    (height_continuous.comp continuous_subtype_val) (value_continuous.comp continuous_subtype_val) parameter
  have equality (other : ℂ) :
      (∫ point : domain, Complex.exp (other * (height point.val : ℂ)) • value point.val ∂subtypeMeasure) =
      ∫ point in domain, Complex.exp (other * (height point : ℂ)) • value point ∂measure := by
    dsimp only [subtypeMeasure]
    rw [integral_subtype_comap compact.measurableSet
      (fun point => Complex.exp (other * (height point : ℂ)) • value point), Measure.restrict_restrict compact.measurableSet,
      Set.inter_self]
  simpa only [equality] using analytic

end TernaryPeriodPolynomials.SphericalDetection.Helpers
