module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs

@[expose] public section


open MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

/-- A uniformly summable family of genuine power series can be integrated coefficientwise. -/
theorem hasFPowerSeriesOnBall_integral_of_uniform_bound
    {X E F : Type} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (measure : Measure X) [IsFiniteMeasure measure]
    (values : E → X → F) (series : X → FormalMultilinearSeries ℝ E F)
    (center : E) (radius : NNReal) (positive : 0 < radius)
    (bound : ℕ → ℝ) (bound_nonnegative : ∀ index, 0 ≤ bound index)
    (summable_bound : Summable (fun index => bound index * (radius : ℝ) ^ index))
    (coefficient_integrable : ∀ index, Integrable (fun parameter => series parameter index) measure)
    (coefficient_bound : ∀ index, ∀ᵐ parameter ∂measure, ‖series parameter index‖ ≤ bound index)
    (expansion : ∀ point : E, ‖point‖ < radius → ∀ᵐ parameter ∂measure,
      HasSum (fun index => (series parameter index) (fun _ => point)) (values (center + point) parameter)) :
    HasFPowerSeriesOnBall (fun point => ∫ parameter, values point parameter ∂measure)
      (fun index => ∫ parameter, series parameter index ∂measure) center radius := by
  let averaged : FormalMultilinearSeries ℝ E F :=
    fun index => ∫ parameter, series parameter index ∂measure
  have averaged_bound (index : ℕ) : ‖averaged index‖ ≤ bound index * measure.real Set.univ :=
    norm_integral_le_of_norm_le_const (coefficient_bound index)
  have averaged_summable : Summable (fun index => ‖averaged index‖ * (radius : ℝ) ^ index) := by
    apply (summable_bound.mul_right (measure.real Set.univ)).of_nonneg_of_le
    · intro index
      positivity
    · intro index
      calc
        _ ≤ (bound index * measure.real Set.univ) * (radius : ℝ) ^ index :=
          mul_le_mul_of_nonneg_right (averaged_bound index) (by positivity)
        _ = _ := by ring
  refine ⟨averaged.le_radius_of_summable averaged_summable, by exact_mod_cast positive, ?_⟩
  intro point inside
  have point_bound : ‖point‖ < (radius : ℝ) := by
    simpa only [Metric.eball_coe, Metric.mem_ball, dist_zero_right] using inside
  have point_summable : Summable (fun index => bound index * ‖point‖ ^ index) := by
    apply summable_bound.of_nonneg_of_le
    · intro index
      exact mul_nonneg (bound_nonnegative index) (pow_nonneg (norm_nonneg point) index)
    · intro index
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg point) point_bound.le index)
        (bound_nonnegative index)
  have evaluated_measurable (index : ℕ) :
      AEStronglyMeasurable (fun parameter => (series parameter index) (fun _ => point)) measure :=
    (continuous_eval_const (fun _ => point)).comp_aestronglyMeasurable
      (coefficient_integrable index).aestronglyMeasurable
  have evaluated_bound (index : ℕ) : ∀ᵐ parameter ∂measure,
      ‖(series parameter index) (fun _ => point)‖ ≤ bound index * ‖point‖ ^ index := by
    filter_upwards [coefficient_bound index] with parameter bounded
    calc
      _ ≤ ‖series parameter index‖ * ‖point‖ ^ index := by
        simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
          (series parameter index).le_opNorm (fun _ => point)
      _ ≤ _ := mul_le_mul_of_nonneg_right bounded (by positivity)
  have integrated := hasSum_integral_of_dominated_convergence
    (μ := measure) (fun index _ => bound index * ‖point‖ ^ index)
    evaluated_measurable evaluated_bound (Filter.Eventually.of_forall (fun _ => point_summable))
    (integrable_const _) (expansion point point_bound)
  convert integrated using 1
  funext index
  exact ContinuousMultilinearMap.integral_apply (coefficient_integrable index) (fun _ => point)

end TernaryPeriodPolynomials.SphericalDetection.Helpers
