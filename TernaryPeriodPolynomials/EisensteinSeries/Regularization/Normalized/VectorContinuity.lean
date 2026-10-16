module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.ExponentialVectorBounds

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Filter

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem normalizedCuspVector_joint_continuous
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) :
    Continuous (fun input : ℂ × AdelicGL => (normalizedCuspVector flat.1 input.1 input.2).val) := by
  apply continuous_iff_continuousAt.mpr
  rintro ⟨parameter, matrix⟩
  let lower : ℝ := parameter.re - 1
  let upper : ℝ := parameter.re + 1
  have first_bound : lower ≤ parameter.re ∧ parameter.re ≤ upper := by dsimp [lower, upper]; constructor <;> linarith
  have bound_continuous : Continuous (fun input : ℂ × AdelicGL =>
      (‖(normalizedCuspVector flat.1 ((lower - 1 : ℝ) : ℂ) input.2).val‖ +
        ‖(normalizedCuspVector flat.1 ((upper + 1 : ℝ) : ℂ) input.2).val‖) * ‖input.1 - parameter‖ +
      ‖(normalizedCuspVector flat.1 parameter input.2).val - (normalizedCuspVector flat.1 parameter matrix).val‖) :=
    ((((normalizedCuspVector_continuous flat.1 _).comp continuous_snd).norm.add
      ((normalizedCuspVector_continuous flat.1 _).comp continuous_snd).norm).mul
      (continuous_fst.sub continuous_const).norm).add
        (((normalizedCuspVector_continuous flat.1 parameter).comp continuous_snd).sub continuous_const).norm
  have bound_limit : Tendsto (fun input : ℂ × AdelicGL =>
      (‖(normalizedCuspVector flat.1 ((lower - 1 : ℝ) : ℂ) input.2).val‖ +
        ‖(normalizedCuspVector flat.1 ((upper + 1 : ℝ) : ℂ) input.2).val‖) * ‖input.1 - parameter‖ +
      ‖(normalizedCuspVector flat.1 parameter input.2).val - (normalizedCuspVector flat.1 parameter matrix).val‖)
      (nhds (parameter, matrix)) (nhds 0) := by
    simpa using (bound_continuous.continuousAt (x := (parameter, matrix))).tendsto
  have open_interval : IsOpen {input : ℂ × AdelicGL | lower < input.1.re ∧ input.1.re < upper} :=
    (isOpen_lt continuous_const (Complex.continuous_re.comp continuous_fst)).inter
      (isOpen_lt (Complex.continuous_re.comp continuous_fst) continuous_const)
  have in_interval : lower < parameter.re ∧ parameter.re < upper := by
    dsimp [lower, upper]
    constructor <;> linarith
  have near : ∀ᶠ input : ℂ × AdelicGL in nhds (parameter, matrix), lower < input.1.re ∧ input.1.re < upper :=
    open_interval.eventually_mem in_interval
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ bound_limit
  filter_upwards [near] with input interval
  calc
    _ ≤ ‖(normalizedCuspVector flat.1 input.1 input.2).val -
          (normalizedCuspVector flat.1 parameter input.2).val‖ +
        ‖(normalizedCuspVector flat.1 parameter input.2).val -
          (normalizedCuspVector flat.1 parameter matrix).val‖ := by
      simpa only [dist_eq_norm] using dist_triangle
        (normalizedCuspVector flat.1 input.1 input.2).val (normalizedCuspVector flat.1 parameter input.2).val
        (normalizedCuspVector flat.1 parameter matrix).val
    _ ≤ _ := add_le_add (normalizedCuspVector_difference_bound flat input.2 lower upper parameter input.1
      first_bound ⟨interval.1.le, interval.2.le⟩) le_rfl

theorem normalizedCuspVector_compact_deriv_bound
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (matrices : Set AdelicGL)
    (compact : IsCompact matrices) (lower upper : ℝ) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ parameter : ℂ, lower ≤ parameter.re → parameter.re ≤ upper →
      ∀ matrix ∈ matrices,
        ‖deriv (fun nearby => (normalizedCuspVector flat.1 nearby matrix).val) parameter‖ ≤ bound := by
  have continuous : Continuous (fun matrix =>
      ‖(normalizedCuspVector flat.1 ((lower - 1 : ℝ) : ℂ) matrix).val‖ +
        ‖(normalizedCuspVector flat.1 ((upper + 1 : ℝ) : ℂ) matrix).val‖) :=
    (normalizedCuspVector_continuous flat.1 _).norm.add (normalizedCuspVector_continuous flat.1 _).norm
  obtain ⟨bound, bounded⟩ := compact.exists_bound_of_continuousOn continuous.continuousOn
  refine ⟨max 0 bound, le_max_left _ _, ?_⟩
  intro parameter lower_bound upper_bound matrix member
  apply (normalizedCuspVector_deriv_norm_le flat matrix lower upper parameter lower_bound upper_bound).trans
  have endpoint_bound := bounded matrix member
  rw [Real.norm_eq_abs, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))] at endpoint_bound
  exact endpoint_bound.trans (le_max_right _ _)

theorem normalizedCuspVector_compact_difference_bound
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (matrices : Set AdelicGL)
    (compact : IsCompact matrices) (lower upper : ℝ) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ first second : ℂ,
      (lower ≤ first.re ∧ first.re ≤ upper) → (lower ≤ second.re ∧ second.re ≤ upper) →
      ∀ matrix ∈ matrices,
        ‖(normalizedCuspVector flat.1 second matrix).val - (normalizedCuspVector flat.1 first matrix).val‖ ≤
          bound * ‖second - first‖ := by
  obtain ⟨bound, nonnegative, bounded⟩ := normalizedCuspVector_compact_deriv_bound flat matrices compact lower upper
  refine ⟨bound, nonnegative, ?_⟩
  intro first second first_bound second_bound matrix member
  exact Convex.norm_image_sub_le_of_norm_deriv_le
    (fun parameter (_ : parameter ∈ Complex.re ⁻¹' Set.Icc lower upper) =>
      (normalizedCuspVector_analytic flat matrix parameter).differentiableAt)
    (fun parameter interval => bounded parameter interval.1 interval.2 matrix member)
    ((convex_Icc lower upper).linear_preimage Complex.reLm) first_bound second_bound

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
