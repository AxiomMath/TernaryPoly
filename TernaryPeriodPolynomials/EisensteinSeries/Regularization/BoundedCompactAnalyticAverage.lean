module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Cusp.RotationSeries

@[expose] public section


open MeasureTheory

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

theorem compact_transformed_analyticAt_bounded
    {X E F : Type*} [MeasurableSpace X] [TopologicalSpace X] [BorelSpace X]
    [CompactSpace X] [T2Space X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (measure : Measure X) [IsProbabilityMeasure measure]
    (function : E → F) (analytic : AnalyticAt ℝ function 0)
    (inner : X → E →L[ℝ] E) (outer : X → F →L[ℝ] F)
    (inner_continuous : ∀ vector, Continuous (fun point => inner point vector))
    (outer_continuous : Continuous (fun input : X × F => outer input.1 input.2))
    (innerBound outerBound : NNReal) (inner_bound : ∀ point, ‖inner point‖ ≤ innerBound)
    (outer_bound : ∀ point, ‖outer point‖ ≤ outerBound) :
    AnalyticAt ℝ (fun vector => ∫ point, outer point (function (inner point vector)) ∂measure) 0 := by
  let scale : ℝ := (outerBound : ℝ) + 1
  have positive : 0 < scale := by dsimp only [scale]; positivity
  let scaled : X → F →L[ℝ] F := fun point => scale⁻¹ • outer point
  have scaled_continuous : Continuous (fun input : X × F => scaled input.1 input.2) :=
    continuous_const.smul outer_continuous
  have scaled_bound (point : X) : ‖scaled point‖ ≤ 1 := by
    change ‖scale⁻¹ • outer point‖ ≤ 1
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr positive)]
    calc
      _ ≤ scale⁻¹ * (outerBound : ℝ) := mul_le_mul_of_nonneg_left (outer_bound point) (inv_nonneg.mpr positive.le)
      _ ≤ scale⁻¹ * scale := mul_le_mul_of_nonneg_left (by dsimp only [scale]; linarith) (inv_nonneg.mpr positive.le)
      _ = 1 := inv_mul_cancel₀ positive.ne'
  have normalized := compact_transformed_analyticAt measure function analytic inner scaled inner_continuous
    scaled_continuous innerBound inner_bound scaled_bound
  have restored := normalized.const_smul (c := scale)
  apply restored.congr
  apply Filter.Eventually.of_forall
  intro vector
  change scale • (∫ point, scale⁻¹ • outer point (function (inner point vector)) ∂measure) = _
  rw [integral_smul, smul_smul, mul_inv_cancel₀ positive.ne', one_smul]

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
