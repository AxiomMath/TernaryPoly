module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.ContinuousMapPowerSeries

@[expose] public section


open Filter

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

theorem analyticAt_continuousMap_local
    {E D F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup D] [NormedSpace ℝ D] [ProperSpace D]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {function : E × D → F} {center : D}
    (analytic : AnalyticAt ℝ function (0, center)) :
    ∃ radius : ℝ, 0 < radius ∧
      ∃ orbit : E → C(Metric.closedBall center radius, F),
        AnalyticAt ℝ orbit 0 ∧
        ∀ᶠ direction in nhds 0, ∀ point : Metric.closedBall center radius,
          orbit direction point = function (direction, point.val) := by
  obtain ⟨series, convergence, expansion⟩ := analytic
  obtain ⟨intermediate, positive, smaller⟩ := exists_between expansion.r_pos
  obtain ⟨radius, radius_eq, radius_lt⟩ := ENNReal.lt_iff_exists_coe.mp smaller
  have radius_positive : (0 : ℝ) < radius := by
    have : (0 : ENNReal) < radius := by simpa only [radius_eq] using positive
    exact ENNReal.coe_pos.mp this
  let X := Metric.closedBall center (radius : ℝ)
  let linear : E →L[ℝ] C(X, E × D) :=
    { toFun := fun direction => ContinuousMap.const X (direction, 0)
      map_add' := by intros; ext point <;> simp
      map_smul' := by intros; ext point <;> simp
      cont := ContinuousMap.continuous_const'.comp (continuous_id.prodMk continuous_const) }
  let offset : C(X, E × D) :=
    ⟨fun point => (0, point.val - center),
      continuous_const.prodMk (continuous_subtype_val.sub continuous_const)⟩
  let input : E → C(X, E × D) := fun direction => linear direction + offset
  have input_analytic : AnalyticAt ℝ input 0 :=
    (linear.analyticAt 0).add analyticAt_const
  have offset_bound : ‖offset‖ ≤ radius := by
    apply (ContinuousMap.norm_le _ radius_positive.le).mpr
    intro point
    change ‖((0 : E), point.val - center)‖ ≤ radius
    simpa only [Prod.norm_def, norm_zero, max_eq_right (norm_nonneg _),
      Metric.mem_closedBall, dist_eq_norm] using
      (show point.val ∈ Metric.closedBall center (radius : ℝ) from point.property)
  have inside : input 0 ∈ Metric.eball 0 convergence := by
    change edist (linear 0 + offset) 0 < convergence
    rw [map_zero, zero_add, edist_zero_right, ← ofReal_norm]
    exact (ENNReal.ofReal_le_ofReal offset_bound).trans_lt (by simpa using radius_lt)
  let orbit : E → C(X, F) := fun direction =>
    (continuousMapPowerSeries (X := X) series).sum (input direction)
  refine ⟨radius, radius_positive, orbit,
    continuousMapPowerSeries_analyticAt_comp expansion input 0 input_analytic inside, ?_⟩
  have near : ∀ᶠ direction in nhds 0, input direction ∈ Metric.eball 0 convergence :=
    input_analytic.continuousAt (Metric.isOpen_eball.mem_nhds inside)
  filter_upwards [near] with direction direction_inside
  intro point
  change (continuousMapPowerSeries (X := X) series).sum (input direction) point = _
  rw [continuousMapPowerSeries_sum_eq expansion (input direction) direction_inside point]
  congr 1
  ext <;> simp [input, linear, offset]

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
