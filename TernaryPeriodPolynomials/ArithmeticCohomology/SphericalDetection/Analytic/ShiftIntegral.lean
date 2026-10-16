module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Analytic.ShiftBound

@[expose] public section


open MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

/-- Weighted compact averages of small translates of one analytic map remain analytic. -/
theorem analyticAt_weighted_shift_integral
    {X E F : Type} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
    [IsScalarTower ℝ ℂ F] [CompleteSpace F]
    (measure : Measure X) [IsFiniteMeasure measure]
    (function : E → F) (series : FormalMultilinearSeries ℝ E F) (center : E) (outerRadius : ENNReal)
    (expansion : HasFPowerSeriesOnBall function series center outerRadius)
    (offset : X → E) (offset_continuous : Continuous offset)
    (kernel : X → ℂ) (kernel_continuous : Continuous kernel)
    (shiftRadius radius : NNReal) (positive : 0 < radius)
    (inside : (shiftRadius : ENNReal) + radius < outerRadius)
    (offset_bound : ∀ parameter, ‖offset parameter‖₊ ≤ shiftRadius) :
    AnalyticAt ℝ (fun point => ∫ parameter, kernel parameter • function (point + offset parameter) ∂measure)
      center := by
  have series_inside : (shiftRadius : ENNReal) + radius < series.radius := inside.trans_le expansion.r_le
  have offset_inside (parameter : X) : (‖offset parameter‖₊ : ENNReal) < outerRadius :=
    lt_of_le_of_lt (by exact_mod_cast offset_bound parameter) (lt_of_le_of_lt le_self_add inside)
  have series_positive : 0 < series.radius := expansion.r_pos.trans_le expansion.r_le
  have shifted_continuous (index : ℕ) : Continuous (fun parameter => series.changeOrigin (offset parameter) index) :=
    (series.hasFPowerSeriesOnBall_changeOrigin index series_positive).continuousOn.comp_continuous
      offset_continuous (by
        intro parameter
        rw [Metric.mem_eball, edist_zero_right]
        exact (offset_inside parameter).trans_le expansion.r_le)
  obtain ⟨kernelBound, kernel_bounded⟩ := isCompact_univ.exists_bound_of_continuousOn kernel_continuous.continuousOn
  let constant : ℝ := max kernelBound 0
  have constant_nonnegative : 0 ≤ constant := le_max_right _ _
  have kernel_bound (parameter : X) : ‖kernel parameter‖ ≤ constant :=
    (kernel_bounded parameter (Set.mem_univ parameter)).trans (le_max_left _ _)
  let coefficients : X → FormalMultilinearSeries ℝ E F :=
    fun parameter index => kernel parameter • series.changeOrigin (offset parameter) index
  have coefficients_integrable (index : ℕ) : Integrable (fun parameter => coefficients parameter index) measure :=
    (kernel_continuous.smul (shifted_continuous index)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have bounds_summable : Summable (fun index =>
      (shiftedSeriesBound series shiftRadius index : ℝ) * (radius : ℝ) ^ index) := by
    simpa only [NNReal.coe_mul, NNReal.coe_pow] using
      NNReal.summable_coe.mpr (shiftedSeriesBound_summable series shiftRadius radius series_inside)
  have integrated := hasFPowerSeriesOnBall_integral_of_uniform_bound measure
    (fun point parameter => kernel parameter • function (point + offset parameter)) coefficients
    center radius positive (fun index => constant * shiftedSeriesBound series shiftRadius index)
    (fun index => mul_nonneg constant_nonnegative (NNReal.coe_nonneg _))
    (by simpa only [mul_assoc] using bounds_summable.mul_left constant)
    coefficients_integrable (by
      intro index
      filter_upwards [] with parameter
      change ‖kernel parameter • series.changeOrigin (offset parameter) index‖ ≤ _
      rw [norm_smul]
      apply mul_le_mul (kernel_bound parameter)
      · exact_mod_cast nnnorm_changeOrigin_le_shiftedSeriesBound series shiftRadius radius positive
          series_inside (offset parameter) (offset_bound parameter) index
      · exact norm_nonneg _
      · exact constant_nonnegative) (by
      intro point point_bound
      filter_upwards [] with parameter
      have reduced_radius : (radius : ENNReal) ≤ outerRadius - (‖offset parameter‖₊ : ENNReal) := by
        have offset_cast : (‖offset parameter‖₊ : ENNReal) ≤ shiftRadius := by
          exact_mod_cast offset_bound parameter
        exact ENNReal.le_sub_of_add_le_left (a := (‖offset parameter‖₊ : ENNReal))
          (b := radius) ENNReal.coe_ne_top ((add_le_add offset_cast (le_refl (radius : ENNReal))).trans inside.le)
      have member : point ∈ Metric.eball 0 (outerRadius - (‖offset parameter‖₊ : ENNReal)) := by
        rw [Metric.mem_eball, edist_zero_right]
        exact lt_of_lt_of_le (by exact_mod_cast point_bound) reduced_radius
      have shifted := ((expansion.changeOrigin (offset_inside parameter)).hasSum member).const_smul (kernel parameter)
      simpa only [coefficients, smul_apply, add_right_comm center] using shifted)
  exact integrated.hasFPowerSeriesAt.analyticAt

end TernaryPeriodPolynomials.SphericalDetection.Helpers
