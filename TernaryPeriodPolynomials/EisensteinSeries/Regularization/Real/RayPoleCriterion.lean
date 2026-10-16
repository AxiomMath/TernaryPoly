module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.UnitaryNormalization

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Filter

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem nonnegative_order_of_bounded_path {Index : Type*} {filter : Filter Index} [filter.NeBot]
    {function : ℂ → ℂ} {point : ℂ} (path : Index → ℂ)
    (approaches : Tendsto path filter (nhdsWithin point {point}ᶜ))
    (bounded : ∃ bound : ℝ, ∀ᶠ index in filter, ‖function (path index)‖ ≤ bound) :
    0 ≤ meromorphicOrderAt function point := by
  obtain ⟨bound, bounded⟩ := bounded
  by_contra negative
  have divergent := (tendsto_cobounded_of_meromorphicOrderAt_neg (lt_of_not_ge negative)).comp approaches
  have large := divergent.eventually (eventually_cobounded_le_norm (bound + 1))
  have impossible : ∀ᶠ index in filter, False := by
    filter_upwards [bounded, large] with index upper lower
    exact (not_le_of_gt (lt_add_one bound)) (lower.trans upper)
  exact impossible.exists.choose_spec

theorem positive_real_ray_tendsto (point : ℂ) :
    Tendsto (fun displacement : ℝ => point + (displacement : ℂ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhdsWithin point {point}ᶜ) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have continuous : ContinuousAt (fun displacement : ℝ => point + (displacement : ℂ)) 0 :=
      continuousAt_const.add Complex.continuous_ofReal.continuousAt
    simpa only [Complex.ofReal_zero, add_zero] using continuous.tendsto.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with displacement positive
    change point + (displacement : ℂ) ≠ point
    intro equality
    have displacement_zero : displacement = 0 := by
      exact Complex.ofReal_eq_zero.mp (add_eq_left.mp equality)
    exact (ne_of_gt positive) displacement_zero

theorem nonnegative_order_of_bounded_real_ray {function : ℂ → ℂ} {point : ℂ}
    (bounded : ∃ bound : ℝ, ∀ᶠ displacement : ℝ in nhdsWithin 0 (Set.Ioi 0),
      ‖function (point + (displacement : ℂ))‖ ≤ bound) :
    0 ≤ meromorphicOrderAt function point :=
  nonnegative_order_of_bounded_path _ (positive_real_ray_tendsto point) bounded

theorem nonnegative_order_of_bounded_square_real_ray {function : ℂ → ℂ} {point : ℂ}
    (bounded : ∃ bound : ℝ, ∀ᶠ displacement : ℝ in nhdsWithin 0 (Set.Ioi 0),
      ‖function (point + (displacement : ℂ))‖ ^ 2 ≤ bound) :
    0 ≤ meromorphicOrderAt function point := by
  obtain ⟨bound, bounded⟩ := bounded
  apply nonnegative_order_of_bounded_real_ray
  refine ⟨max bound 1, ?_⟩
  filter_upwards [bounded] with displacement square_bound
  have first : bound ≤ max bound 1 := le_max_left _ _
  have second : 1 ≤ max bound 1 := le_max_right _ _
  have norm_positive := norm_nonneg (function (point + (displacement : ℂ)))
  nlinarith

theorem nonnegative_order_of_subtracted_square_nonnegative
    {function : ℂ → ℂ} {point : ℂ} (constant coefficient : ℝ → ℝ)
    (constant_continuous : ContinuousAt constant 0) (coefficient_continuous : ContinuousAt coefficient 0)
    (coefficient_positive : 0 < coefficient 0)
    (nonnegative : ∀ᶠ displacement : ℝ in nhdsWithin 0 (Set.Ioi 0),
      0 ≤ constant displacement - coefficient displacement *
        ‖function (point + (displacement : ℂ))‖ ^ 2) :
    0 ≤ meromorphicOrderAt function point := by
  have constant_bound : ∀ᶠ displacement in nhds (0 : ℝ), constant displacement < constant 0 + 1 :=
    constant_continuous.eventually (gt_mem_nhds (lt_add_one _))
  have coefficient_bound : ∀ᶠ displacement in nhds (0 : ℝ), coefficient 0 / 2 < coefficient displacement :=
    coefficient_continuous.eventually (lt_mem_nhds (by linarith))
  apply nonnegative_order_of_bounded_square_real_ray
  refine ⟨max (constant 0 + 1) 0 / (coefficient 0 / 2), ?_⟩
  filter_upwards [nonnegative, constant_bound.filter_mono nhdsWithin_le_nhds,
    coefficient_bound.filter_mono nhdsWithin_le_nhds] with displacement nonnegative upper lower
  apply (le_div_iff₀ (by linarith : 0 < coefficient 0 / 2)).mpr
  have square_nonnegative := sq_nonneg ‖function (point + (displacement : ℂ))‖
  have upper_max : constant 0 + 1 ≤ max (constant 0 + 1) 0 := le_max_left _ _
  nlinarith

theorem regularization_of_unitary_real_ray_bound
    {degree : ℕ} {family continuation : ℂ → AdelicGL → ℂ}
    (continuation_spec : IsEisensteinContinuation family continuation)
    (bounded : ∀ matrix, ∃ bound : ℝ, ∀ᶠ displacement : ℝ in nhdsWithin 0 (Set.Ioi 0),
      ‖unitaryNormalize degree continuation ((degree : ℂ) / 2 + (displacement : ℂ)) matrix‖ ≤ bound) :
    ∃ repaired : ℂ → AdelicGL → ℂ,
      IsEisensteinContinuation family repaired ∧ SameOffCohomologicalPoint continuation repaired ∧
        ∀ matrix, AnalyticAt ℂ (fun parameter => repaired parameter matrix) cohomologicalPoint := by
  apply regularization_of_unitaryNormalize_order continuation_spec
  intro matrix
  exact nonnegative_order_of_bounded_real_ray (bounded matrix)

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
