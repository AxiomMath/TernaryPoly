module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Cusp.SegmentDerivative
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.AnalyticSegmentDerivative

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix Filter
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

theorem cusp_family_local_scalar_difference_bound
    {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [ProperSpace D]
    {cusp : CuspidalRepresentation} {degree : ℕ} (cohomological : Cohomological cusp degree)
    (family : D → cuspFiniteFixedSubmodule cusp binaryPrincipalLevel) (center : D)
    (analytic : AnalyticAt ℝ
      (fun input : Matrix (Fin 2) (Fin 2) ℝ × D =>
        cuspCenteredMatrixOrbit cusp (family input.2).val.val input.1) (0, center)) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ᶠ displacement in nhds 0,
      ‖cuspBoundedRealization cusp (family (center + displacement)).val -
        cuspBoundedRealization cusp (family center).val‖ ≤ constant * ‖displacement‖ := by
  obtain ⟨lifted, equality, bound, nonnegative, bounded⟩ :=
    cusp_family_segment_scalar_bound cohomological family center analytic
  have neighborhood : {pair : D × D | (lifted pair).val.val =
      segmentDerivativeAverage (fun point => (family point).val.val) center pair.1 pair.2 ∧
      ‖cuspBoundedRealization cusp (lifted pair).val‖ ≤ bound} ∈ nhds 0 := equality.and bounded
  obtain ⟨radius, positive, estimates⟩ := Metric.mem_nhds_iff.mp neighborhood
  have family_analytic : AnalyticAt ℝ (fun point => (family point).val.val) center := by
    simpa only [Function.comp_def, cuspCenteredMatrixOrbit_zero] using analytic.comp
      (f := fun point : D => ((0 : Matrix (Fin 2) (Fin 2) ℝ), point))
      (analyticAt_const.prod analyticAt_id)
  have difference := segmentDerivativeAverage_self_eventually family_analytic
  refine ⟨2 * bound / radius, by positivity, ?_⟩
  filter_upwards [difference, Metric.ball_mem_nhds (0 : D) positive] with displacement difference_eq small
  by_cases zero : displacement = 0
  · simp [zero]
  have norm_positive : 0 < ‖displacement‖ := norm_pos_iff.mpr zero
  let scalar : ℝ := radius / (2 * ‖displacement‖)
  have scalar_positive : 0 < scalar := by dsimp [scalar]; positivity
  have scaled_norm : ‖scalar • displacement‖ = radius / 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos scalar_positive]
    dsimp [scalar]
    field_simp
  have pair_small : (displacement, scalar • displacement) ∈ Metric.ball (0 : D × D) radius := by
    rw [Metric.mem_ball, dist_zero_right, Prod.norm_def, max_lt_iff]
    exact ⟨by simpa using small, by rw [scaled_norm]; linarith⟩
  obtain ⟨value_eq, scalar_bound⟩ := estimates pair_small
  have vector_eq : (lifted (displacement, scalar • displacement)).val =
      (scalar : ℂ) • ((family (center + displacement)).val - (family center).val) := by
    apply Subtype.ext
    change (lifted (displacement, scalar • displacement)).val.val =
      (scalar : ℂ) • ((family (center + displacement)).val.val - (family center).val.val)
    rw [value_eq, segmentDerivativeAverage_smul_direction, difference_eq]
    exact (RCLike.real_smul_eq_coe_smul (K := ℂ) _ _)
  rw [vector_eq, map_smul, map_sub, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos scalar_positive] at scalar_bound
  rw [mul_comm scalar] at scalar_bound
  have target := (le_div_iff₀ scalar_positive).mpr scalar_bound
  calc
    _ ≤ bound / scalar := target
    _ = (2 * bound / radius) * ‖displacement‖ := by dsimp [scalar]; field_simp

theorem cusp_family_local_scalar_continuousAt
    {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [ProperSpace D]
    {cusp : CuspidalRepresentation} {degree : ℕ} (cohomological : Cohomological cusp degree)
    (family : D → cuspFiniteFixedSubmodule cusp binaryPrincipalLevel) (center : D)
    (analytic : AnalyticAt ℝ
      (fun input : Matrix (Fin 2) (Fin 2) ℝ × D =>
        cuspCenteredMatrixOrbit cusp (family input.2).val.val input.1) (0, center)) :
    ContinuousAt (fun point => cuspBoundedRealization cusp (family point).val) center := by
  obtain ⟨constant, _, bounded⟩ := cusp_family_local_scalar_difference_bound cohomological family center analytic
  have difference_continuous : Tendsto (fun point : D => point - center) (nhds center) (nhds 0) :=
    by simpa only [sub_self] using (show Continuous (fun point : D => point - center) from continuous_id.sub continuous_const).tendsto center
  have bound_near := difference_continuous.eventually bounded
  have limit : Tendsto (fun point : D => constant * ‖point - center‖) (nhds center) (nhds 0) := by
    simpa only [norm_zero, mul_zero] using difference_continuous.norm.const_mul constant
  apply Metric.continuousAt_iff'.mpr
  intro epsilon positive
  filter_upwards [bound_near, limit.eventually (gt_mem_nhds positive)] with point estimate small
  rw [dist_eq_norm]
  have identity : center + (point - center) = point := by abel
  rw [identity] at estimate
  exact estimate.trans_lt small

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
