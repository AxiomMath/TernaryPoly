module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.ScaledExponentialBounds

@[expose] public section


open Filter

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem exponential_vector_family_joint_continuous
    {X E : Type*} [TopologicalSpace X] [NormedAddCommGroup E] [NormedSpace ℂ E]
    (family : ℂ → X → E) (continuous : ∀ parameter, Continuous (family parameter))
    (exponential : ∀ point, ∃ weight : ℝ, ∀ parameter,
      family parameter point = Complex.exp (parameter * (weight : ℂ)) • family 0 point) :
    Continuous (fun input : ℂ × X => family input.1 input.2) := by
  apply continuous_iff_continuousAt.mpr
  rintro ⟨parameter, point⟩
  let lower : ℝ := parameter.re - 1
  let upper : ℝ := parameter.re + 1
  have first_bound : lower ≤ parameter.re ∧ parameter.re ≤ upper := by
    dsimp [lower, upper]
    constructor <;> linarith
  have bound_continuous : Continuous (fun input : ℂ × X =>
      (‖family ((lower - 1 : ℝ) : ℂ) input.2‖ + ‖family ((upper + 1 : ℝ) : ℂ) input.2‖) *
        ‖input.1 - parameter‖ + ‖family parameter input.2 - family parameter point‖) :=
    ((((continuous _).comp continuous_snd).norm.add
      ((continuous _).comp continuous_snd).norm).mul
      (continuous_fst.sub continuous_const).norm).add
        (((continuous parameter).comp continuous_snd).sub continuous_const).norm
  have bound_limit : Tendsto (fun input : ℂ × X =>
      (‖family ((lower - 1 : ℝ) : ℂ) input.2‖ + ‖family ((upper + 1 : ℝ) : ℂ) input.2‖) *
        ‖input.1 - parameter‖ + ‖family parameter input.2 - family parameter point‖)
      (nhds (parameter, point)) (nhds 0) := by
    simpa using (bound_continuous.continuousAt (x := (parameter, point))).tendsto
  have open_interval : IsOpen {input : ℂ × X | lower < input.1.re ∧ input.1.re < upper} :=
    (isOpen_lt continuous_const (Complex.continuous_re.comp continuous_fst)).inter
      (isOpen_lt (Complex.continuous_re.comp continuous_fst) continuous_const)
  have in_interval : lower < parameter.re ∧ parameter.re < upper := by
    dsimp [lower, upper]
    constructor <;> linarith
  have near : ∀ᶠ input : ℂ × X in nhds (parameter, point), lower < input.1.re ∧ input.1.re < upper :=
    open_interval.eventually_mem in_interval
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ bound_limit
  filter_upwards [near] with input interval
  have difference : ‖family input.1 input.2 - family parameter input.2‖ ≤
      (‖family ((lower - 1 : ℝ) : ℂ) input.2‖ + ‖family ((upper + 1 : ℝ) : ℂ) input.2‖) *
        ‖input.1 - parameter‖ := by
    obtain ⟨weight, scaling⟩ := exponential input.2
    rw [scaling input.1, scaling parameter, scaling ((lower - 1 : ℝ) : ℂ), scaling ((upper + 1 : ℝ) : ℂ)]
    exact exponential_vector_difference_bound _ weight lower upper parameter input.1 first_bound
      ⟨interval.1.le, interval.2.le⟩
  exact (norm_sub_le_norm_sub_add_norm_sub _ (family parameter input.2) _).trans
    (add_le_add difference le_rfl)

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
