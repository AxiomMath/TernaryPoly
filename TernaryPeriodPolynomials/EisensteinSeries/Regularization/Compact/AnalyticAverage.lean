module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Compact.PowerSeriesIntegral

@[expose] public section


open MeasureTheory

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

variable {X E F : Type*} [MeasurableSpace X] [TopologicalSpace X] [BorelSpace X]
  [CompactSpace X] [T2Space X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

noncomputable def transformedPowerSeries (series : FormalMultilinearSeries ℝ E F)
    (inner : E →L[ℝ] E) (outer : F →L[ℝ] F) : FormalMultilinearSeries ℝ E F :=
  fun order => outer.compContinuousMultilinearMap
    ((series order).compContinuousLinearMap (fun _ => inner))

theorem transformedPowerSeries_apply (series : FormalMultilinearSeries ℝ E F)
    (inner : E →L[ℝ] E) (outer : F →L[ℝ] F) (order : ℕ) (vectors : Fin order → E) :
    transformedPowerSeries series inner outer order vectors =
      outer (series order (fun index => inner (vectors index))) := rfl

theorem transformedPowerSeries_norm_le (series : FormalMultilinearSeries ℝ E F)
    (inner : E →L[ℝ] E) (outer : F →L[ℝ] F)
    (bound : NNReal) (inner_bound : ‖inner‖ ≤ bound) (outer_bound : ‖outer‖ ≤ 1) (order : ℕ) :
    ‖transformedPowerSeries series inner outer order‖ ≤ ‖series order‖ * (bound : ℝ) ^ order := by
  calc
    _ ≤ ‖outer‖ * ‖(series order).compContinuousLinearMap (fun _ => inner)‖ :=
      outer.norm_compContinuousMultilinearMap_le _
    _ ≤ ‖(series order).compContinuousLinearMap (fun _ => inner)‖ := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right outer_bound (norm_nonneg _)
    _ ≤ ‖series order‖ * ‖inner‖ ^ order := by
      simpa using (series order).norm_compContinuousLinearMap_le (fun _ => inner)
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) inner_bound order) (norm_nonneg _)

theorem compact_transformed_analyticAt (measure : Measure X) [IsProbabilityMeasure measure]
    (function : E → F) (analytic : AnalyticAt ℝ function 0)
    (inner : X → E →L[ℝ] E) (outer : X → F →L[ℝ] F)
    (inner_continuous : ∀ vector, Continuous (fun point => inner point vector))
    (outer_continuous : Continuous (fun input : X × F => outer input.1 input.2))
    (bound : NNReal) (inner_bound : ∀ point, ‖inner point‖ ≤ bound)
    (outer_bound : ∀ point, ‖outer point‖ ≤ 1) :
    AnalyticAt ℝ (fun vector => ∫ point, outer point (function (inner point vector)) ∂measure) 0 := by
  obtain ⟨series, original_radius, expansion⟩ := analytic
  obtain ⟨radius, radius_positive, small_radius⟩ := ENNReal.exists_nnreal_pos_mul_lt
    (a := (bound : ENNReal)) (b := original_radius) ENNReal.coe_ne_top expansion.r_pos.ne'
  let coefficients := fun point => transformedPowerSeries series (inner point) (outer point)
  have coefficient_continuous : ∀ order vectors, Continuous (fun point => coefficients point order vectors) := by
    intro order vectors
    change Continuous (fun point => outer point (series order (fun index => inner point (vectors index))))
    exact outer_continuous.comp (continuous_id.prodMk ((series order).cont.comp
      (continuous_pi (fun index => inner_continuous (vectors index)))))
  have coefficient_bound := fun point order =>
    transformedPowerSeries_norm_le series (inner point) (outer point) bound (inner_bound point) (outer_bound point) order
  have summable : Summable (fun order => (‖series order‖ * (bound : ℝ) ^ order) * (radius : ℝ) ^ order) := by
    have original := series.summable_norm_mul_pow (r := radius * bound)
      (by simpa only [ENNReal.coe_mul] using small_radius.trans_le expansion.r_le)
    simpa only [NNReal.coe_mul, mul_pow, mul_assoc, mul_comm (radius : ℝ)] using original
  apply compactPowerSeriesIntegral_analyticAt measure coefficients
    (fun point vector => outer point (function (inner point vector))) coefficient_continuous
    (fun order => ‖series order‖ * (bound : ℝ) ^ order)
    (fun order => mul_nonneg (norm_nonneg _) (pow_nonneg bound.coe_nonneg order))
    coefficient_bound radius radius_positive summable
  intro point vector inside
  have image_bound : ‖inner point vector‖ ≤ (radius * bound : NNReal) := by
    calc
      _ ≤ ‖inner point‖ * ‖vector‖ := (inner point).le_opNorm vector
      _ ≤ (bound : ℝ) * radius := mul_le_mul (inner_bound point) inside.le (norm_nonneg _) bound.coe_nonneg
      _ = _ := by simp only [NNReal.coe_mul, mul_comm]
  have image_inside : inner point vector ∈ Metric.eball 0 original_radius := by
    rw [Metric.mem_eball, edist_zero_right]
    apply lt_of_le_of_lt _ small_radius
    rw [← ENNReal.coe_mul]
    exact_mod_cast image_bound
  simpa only [zero_add, coefficients, transformedPowerSeries_apply] using
    (outer point).hasSum (expansion.hasSum image_inside)

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
