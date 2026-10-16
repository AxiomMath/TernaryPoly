module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Compact.MultilinearIntegral

@[expose] public section


open MeasureTheory

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

variable {X E F : Type*} [MeasurableSpace X] [TopologicalSpace X] [BorelSpace X]
  [CompactSpace X] [T2Space X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

noncomputable def compactPowerSeriesIntegral (measure : Measure X) [IsProbabilityMeasure measure]
    (coefficients : X → FormalMultilinearSeries ℝ E F)
    (continuous : ∀ order vectors, Continuous (fun point => coefficients point order vectors))
    (bounds : ℕ → ℝ) (bounded : ∀ point order, ‖coefficients point order‖ ≤ bounds order) :
    FormalMultilinearSeries ℝ E F :=
  fun order => compactMultilinearIntegral measure (fun point => coefficients point order)
    (continuous order) (bounds order) (fun point => bounded point order)

theorem compactPowerSeriesIntegral_hasFPowerSeriesOnBall
    (measure : Measure X) [IsProbabilityMeasure measure]
    (coefficients : X → FormalMultilinearSeries ℝ E F) (family : X → E → F)
    (continuous : ∀ order vectors, Continuous (fun point => coefficients point order vectors))
    (bounds : ℕ → ℝ) (bounds_nonnegative : ∀ order, 0 ≤ bounds order)
    (bounded : ∀ point order, ‖coefficients point order‖ ≤ bounds order)
    (radius : NNReal) (radius_positive : 0 < radius)
    (summable : Summable (fun order => bounds order * (radius : ℝ) ^ order))
    (expansions : ∀ point vector, ‖vector‖ < radius →
      HasSum (fun order => coefficients point order (fun _ => vector)) (family point vector)) :
    HasFPowerSeriesOnBall (fun vector => ∫ point, family point vector ∂measure)
      (compactPowerSeriesIntegral measure coefficients continuous bounds bounded) 0 radius := by
  refine ⟨?_, by exact_mod_cast radius_positive, ?_⟩
  · apply FormalMultilinearSeries.le_radius_of_bound _
      (∑' order, bounds order * (radius : ℝ) ^ order)
    intro order
    apply le_trans (mul_le_mul_of_nonneg_right
      (compactMultilinearIntegral_norm_le measure (fun point => coefficients point order)
        (continuous order) (bounds order) (bounds_nonnegative order) (fun point => bounded point order))
      (pow_nonneg radius.coe_nonneg order))
    exact summable.le_tsum order (fun index _ => mul_nonneg (bounds_nonnegative index)
      (pow_nonneg radius.coe_nonneg index))
  · intro vector inside
    have small : ‖vector‖ < radius := by
      simpa only [Metric.eball_coe, Metric.mem_ball, dist_zero_right] using inside
    have integrable : ∀ order, Integrable (fun point => coefficients point order (fun _ => vector)) measure :=
      fun order => compact_multilinear_integrable measure (fun point => coefficients point order)
        (continuous order) _
    have term_bound (point : X) (order : ℕ) :
        ‖coefficients point order (fun _ => vector)‖ ≤ bounds order * (radius : ℝ) ^ order := by
      calc
        _ ≤ ‖coefficients point order‖ * ‖vector‖ ^ order := by
          simpa using (coefficients point order).le_opNorm (fun _ => vector)
        _ ≤ bounds order * (radius : ℝ) ^ order :=
          mul_le_mul (bounded point order) (pow_le_pow_left₀ (norm_nonneg _) small.le order)
            (pow_nonneg (norm_nonneg _) order) (bounds_nonnegative order)
    have integral_summable : Summable (fun order =>
        ∫ point, ‖coefficients point order (fun _ => vector)‖ ∂measure) := by
      apply Summable.of_nonneg_of_le
        (fun order => integral_nonneg (fun point => norm_nonneg _)) _ summable
      intro order
      calc
        _ ≤ ∫ _ : X, bounds order * (radius : ℝ) ^ order ∂measure :=
          integral_mono (integrable order).norm (integrable_const _) (fun point => term_bound point order)
        _ = _ := by simp
    have integrated := hasSum_integral_of_summable_integral_norm integrable integral_summable
    have value : (∫ point, ∑' order, coefficients point order (fun _ => vector) ∂measure) =
        ∫ point, family point vector ∂measure := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun point => (expansions point vector small).tsum_eq)
    simpa only [zero_add, compactPowerSeriesIntegral, compactMultilinearIntegral_apply, value] using integrated

theorem compactPowerSeriesIntegral_analyticAt
    (measure : Measure X) [IsProbabilityMeasure measure]
    (coefficients : X → FormalMultilinearSeries ℝ E F) (family : X → E → F)
    (continuous : ∀ order vectors, Continuous (fun point => coefficients point order vectors))
    (bounds : ℕ → ℝ) (bounds_nonnegative : ∀ order, 0 ≤ bounds order)
    (bounded : ∀ point order, ‖coefficients point order‖ ≤ bounds order)
    (radius : NNReal) (radius_positive : 0 < radius)
    (summable : Summable (fun order => bounds order * (radius : ℝ) ^ order))
    (expansions : ∀ point vector, ‖vector‖ < radius →
      HasSum (fun order => coefficients point order (fun _ => vector)) (family point vector)) :
    AnalyticAt ℝ (fun vector => ∫ point, family point vector ∂measure) 0 :=
  (compactPowerSeriesIntegral_hasFPowerSeriesOnBall measure coefficients family continuous bounds
    bounds_nonnegative bounded radius radius_positive summable expansions).analyticAt

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
