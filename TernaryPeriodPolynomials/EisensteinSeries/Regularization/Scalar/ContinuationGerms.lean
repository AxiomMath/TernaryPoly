module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.LargeDegreeRegularization
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Real.RayPoleCriterion

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Filter

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem normalized_continuation_germ_actual_sum
    {degree : ℕ} {inducingData : InducingData degree} {family continuation : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family)
    (continuation_spec : IsEisensteinContinuation family continuation)
    (matrix : AdelicGL) (point : ℂ) (large : 3 / 2 < point.re) :
    (fun parameter => unitaryNormalize degree continuation parameter matrix) =ᶠ[nhdsWithin point {point}ᶜ]
      (fun parameter => ∑' flag, eisensteinSummand (unitaryNormalize degree family) parameter matrix flag) := by
  obtain ⟨sum_analytic, summable⟩ := normalized_scalar_sum_analytic flat matrix
  have normalized_spec := unitaryNormalize_continuation degree continuation_spec
  obtain ⟨threshold, convergence⟩ := normalized_spec.2
  let actualSum (parameter : ℂ) :=
    ∑' flag, eisensteinSummand (unitaryNormalize degree family) parameter matrix flag
  let base : ℂ := (max threshold (3 / 2) + 1 : ℝ)
  have base_large : 3 / 2 < base.re := by
    dsimp [base]
    linarith [le_max_right threshold (3 / 2)]
  have base_threshold : threshold < base.re := by
    dsimp [base]
    linarith [le_max_left threshold (3 / 2)]
  have same_near_base : (fun parameter => unitaryNormalize degree continuation parameter matrix) =ᶠ[nhds base]
      actualSum := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).eventually_mem base_large,
      (isOpen_lt continuous_const Complex.continuous_re).eventually_mem base_threshold]
      with parameter parameter_large parameter_threshold
    exact (convergence parameter parameter_threshold matrix).unique (summable parameter parameter_large).hasSum
  have difference_meromorphic : MeromorphicOn
      (fun parameter => unitaryNormalize degree continuation parameter matrix - actualSum parameter)
      {parameter : ℂ | 3 / 2 < parameter.re} := by
    intro parameter parameter_large
    exact (normalized_spec.1 matrix parameter).sub (sum_analytic parameter parameter_large).meromorphicAt
  have zero_order_base : meromorphicOrderAt
      (fun parameter => unitaryNormalize degree continuation parameter matrix - actualSum parameter) base = ⊤ := by
    apply meromorphicOrderAt_eq_top_iff.mpr
    filter_upwards [same_near_base.filter_mono nhdsWithin_le_nhds] with parameter equality
    exact sub_eq_zero.mpr equality
  have zero_order_point : meromorphicOrderAt
      (fun parameter => unitaryNormalize degree continuation parameter matrix - actualSum parameter) point = ⊤ := by
    by_contra nonzero
    exact (difference_meromorphic.meromorphicOrderAt_ne_top_of_isPreconnected
      ((convex_Ioi (3 / 2)).linear_preimage Complex.reLm).isPreconnected large base_large nonzero) zero_order_base
  filter_upwards [meromorphicOrderAt_eq_top_iff.mp zero_order_point] with parameter equality
  exact sub_eq_zero.mp equality

theorem normalized_continuation_eq_actual_sum_of_continuousAt
    {degree : ℕ} {inducingData : InducingData degree} {family continuation : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family)
    (continuation_spec : IsEisensteinContinuation family continuation)
    (matrix : AdelicGL) (point : ℂ) (large : 3 / 2 < point.re)
    (continuous : ContinuousAt (fun parameter => unitaryNormalize degree continuation parameter matrix) point) :
    unitaryNormalize degree continuation point matrix =
      ∑' flag, eisensteinSummand (unitaryNormalize degree family) point matrix flag := by
  have sum_continuous := ((normalized_scalar_sum_analytic flat matrix).1 point large).continuousAt
  exact ((continuous.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE sum_continuous).mp
    (normalized_continuation_germ_actual_sum flat continuation_spec matrix point large)).eq_of_nhds

theorem normalized_continuation_boundary_ray_eq_actual_sum
    {degree : ℕ} {inducingData : InducingData degree} {family continuation : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family)
    (continuation_spec : IsEisensteinContinuation family continuation) (matrix : AdelicGL) :
    ∀ᶠ displacement : ℝ in nhdsWithin 0 (Set.Ioi 0),
      unitaryNormalize degree continuation ((3 : ℂ) / 2 + (displacement : ℂ)) matrix =
        ∑' flag, eisensteinSummand (unitaryNormalize degree family)
          ((3 : ℂ) / 2 + (displacement : ℂ)) matrix flag := by
  have analytic := (unitaryNormalize_continuation degree continuation_spec).1 matrix ((3 : ℂ) / 2)
    |>.eventually_analyticAt
  have along_ray := (positive_real_ray_tendsto ((3 : ℂ) / 2)).eventually analytic
  filter_upwards [along_ray, self_mem_nhdsWithin] with displacement analytic positive
  apply normalized_continuation_eq_actual_sum_of_continuousAt flat continuation_spec matrix _ _ analytic.continuousAt
  change 0 < displacement at positive
  norm_num
  exact positive

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
