module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.GlobalParameterBounds
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.SectionParameterContinuity

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix Filter

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem real_exponential_canonical_weight (family : ℂ → ℂ) (base : ℂ) (weight : ℝ)
    (scaling : ∀ parameter, family parameter =
      Complex.exp ((parameter - base) * (weight : ℂ)) * family base) (parameter : ℂ) :
    family parameter = Complex.exp ((parameter - base) *
      ((Real.log ‖family (base + 1)‖ - Real.log ‖family base‖ : ℝ) : ℂ)) * family base := by
  by_cases zero : family base = 0
  · simp [scaling parameter, zero]
  · have step : ‖family (base + 1)‖ = Real.exp weight * ‖family base‖ := by
      rw [scaling (base + 1)]
      have difference : base + 1 - base = 1 := by ring
      simp only [difference, one_mul, norm_mul, Complex.norm_exp, Complex.ofReal_re]
    rw [step, Real.log_mul (Real.exp_ne_zero _) (norm_ne_zero_iff.mpr zero),
      Real.log_exp, add_sub_cancel_right]
    exact scaling parameter

theorem real_exponential_joint_continuous {X : Type*} [TopologicalSpace X]
    (family : ℂ → X → ℂ) (base : ℂ)
    (continuous : ∀ parameter, Continuous (family parameter))
    (exponential : ∀ point, ∃ weight : ℝ, ∀ parameter,
      family parameter point = Complex.exp ((parameter - base) * (weight : ℂ)) * family base point) :
    Continuous (fun input : ℂ × X => family input.1 input.2) := by
  apply continuous_iff_continuousAt.mpr
  rintro ⟨parameter, point⟩
  obtain ⟨weight, scaling⟩ := exponential point
  by_cases zero : family base point = 0
  · have all_zero (nearby : ℂ) : family nearby point = 0 := by rw [scaling nearby, zero, mul_zero]
    let lower : ℂ := parameter - 1
    let upper : ℂ := parameter + 1
    have bound_continuous : ContinuousAt (fun input : ℂ × X =>
        ‖family lower input.2‖ + ‖family upper input.2‖) (parameter, point) :=
      (((continuous lower).comp continuous_snd).norm.add ((continuous upper).comp continuous_snd).norm).continuousAt
    have bound_limit : Tendsto (fun input : ℂ × X => ‖family lower input.2‖ + ‖family upper input.2‖)
        (nhds (parameter, point)) (nhds 0) := by
      simpa only [all_zero, norm_zero, zero_add] using bound_continuous.tendsto
    have open_interval : IsOpen {input : ℂ × X | lower.re < input.1.re ∧ input.1.re < upper.re} :=
      (isOpen_lt continuous_const (Complex.continuous_re.comp continuous_fst)).inter
        (isOpen_lt (Complex.continuous_re.comp continuous_fst) continuous_const)
    have in_interval : lower.re < parameter.re ∧ parameter.re < upper.re := by
      simp [lower, upper]
    have near : ∀ᶠ input : ℂ × X in nhds (parameter, point),
        lower.re < input.1.re ∧ input.1.re < upper.re := open_interval.eventually_mem in_interval
    change Tendsto _ _ (nhds (family parameter point))
    rw [all_zero]
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ bound_limit
    filter_upwards [near] with input bounds
    obtain ⟨nearbyWeight, nearby_scaling⟩ := exponential input.2
    rw [nearby_scaling input.1, nearby_scaling lower, nearby_scaling upper]
    exact real_exponential_norm_le_endpoints _ _ _ _ _ nearbyWeight bounds.1.le bounds.2.le
  · have next_nonzero : family (base + 1) point ≠ 0 := by
      rw [scaling (base + 1)]
      exact mul_ne_zero (Complex.exp_ne_zero _) zero
    have base_continuous : ContinuousAt (fun input : ℂ × X => ‖family base input.2‖) (parameter, point) :=
      ((continuous base).comp continuous_snd).norm.continuousAt
    have next_continuous : ContinuousAt (fun input : ℂ × X => ‖family (base + 1) input.2‖) (parameter, point) :=
      ((continuous (base + 1)).comp continuous_snd).norm.continuousAt
    have weight_continuous : ContinuousAt (fun input : ℂ × X =>
        Real.log ‖family (base + 1) input.2‖ - Real.log ‖family base input.2‖) (parameter, point) :=
      (next_continuous.log (norm_ne_zero_iff.mpr next_nonzero)).sub
        (base_continuous.log (norm_ne_zero_iff.mpr zero))
    have model_continuous : ContinuousAt (fun input : ℂ × X =>
        Complex.exp ((input.1 - base) *
          ((Real.log ‖family (base + 1) input.2‖ - Real.log ‖family base input.2‖ : ℝ) : ℂ)) *
          family base input.2) (parameter, point) :=
      (((continuous_fst.continuousAt.sub continuousAt_const).mul
        (Complex.continuous_ofReal.continuousAt.comp weight_continuous)).cexp).mul
        ((continuous base).comp continuous_snd).continuousAt
    apply model_continuous.congr_of_eventuallyEq
    apply Eventually.of_forall
    intro input
    obtain ⟨nearbyWeight, nearby_scaling⟩ := exponential input.2
    exact real_exponential_canonical_weight (fun nearby => family nearby input.2) base
      nearbyWeight nearby_scaling input.1

theorem flat_section_joint_continuous
    {degree : ℕ} {inducingData : InducingData degree}
    {family : ℂ → AdelicGL → ℂ} (flat : IsFlatSection inducingData family) :
    Continuous (fun input : ℂ × AdelicGL => family input.1 input.2) :=
  real_exponential_joint_continuous family cohomologicalPoint
    (fun parameter => induced_continuous (flat.1 parameter)) (flat_section_real_exponential flat)

theorem flat_section_compact_bound
    {degree : ℕ} {inducingData : InducingData degree}
    {family : ℂ → AdelicGL → ℂ} (flat : IsFlatSection inducingData family)
    (parameters : Set ℂ) (matrices : Set AdelicGL)
    (parameters_compact : IsCompact parameters) (matrices_compact : IsCompact matrices) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ parameter ∈ parameters, ∀ matrix ∈ matrices,
      ‖family parameter matrix‖ ≤ bound := by
  obtain ⟨bound, bounded⟩ := (parameters_compact.prod matrices_compact).exists_bound_of_continuousOn
    (flat_section_joint_continuous flat).continuousOn
  exact ⟨max 0 bound, le_max_left _ _, fun parameter parameter_in matrix matrix_in =>
    (bounded (parameter, matrix) ⟨parameter_in, matrix_in⟩).trans (le_max_right _ _)⟩

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
