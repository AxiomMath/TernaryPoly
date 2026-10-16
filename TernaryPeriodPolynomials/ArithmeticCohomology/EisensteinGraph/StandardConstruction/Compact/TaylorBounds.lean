module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.TranslatedSeries

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open Filter Topology
open scoped NNReal

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.CompactTaylorBounds

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

def coefficients (function : E → F) (center : E) : FormalMultilinearSeries ℝ E F :=
  fun order => (order.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ order function center

theorem coefficients_norm_le {function : E → F} {series : FormalMultilinearSeries ℝ E F}
    {center : E} {radius : ENNReal} (expansion : HasFPowerSeriesOnBall function series center radius)
    (order : ℕ) : ‖coefficients function center order‖ ≤ ‖series order‖ := by
  have positive : (0 : ℝ) < order.factorial := by exact_mod_cast order.factorial_pos
  change ‖(order.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ order function center‖ ≤ _
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr positive.le)]
  calc
    _ ≤ (order.factorial : ℝ)⁻¹ * ((order.factorial : ℝ) * ‖series order‖) :=
      mul_le_mul_of_nonneg_left
        (TernaryPeriodPolynomials.PlaneEisensteinContinuation.AnalyticDerivatives.powerSeries_iteratedFDeriv_norm_le expansion order)
        (inv_nonneg.mpr positive.le)
    _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ positive.ne', one_mul]

omit [CompleteSpace F] in
theorem radius_of_coefficient_bound (series : FormalMultilinearSeries ℝ E F)
    (radius : ℝ≥0) (positive : 0 < radius) (constant : ℝ)
    (bound : ∀ order, ‖series order‖ ≤ constant * (radius : ℝ)⁻¹ ^ order) :
    (radius : ENNReal) ≤ series.radius := by
  have nonzero : (radius : ℝ) ≠ 0 := by exact_mod_cast positive.ne'
  apply series.le_radius_of_bound constant
  intro order
  calc
    ‖series order‖ * (radius : ℝ) ^ order ≤
        (constant * (radius : ℝ)⁻¹ ^ order) * (radius : ℝ) ^ order :=
      mul_le_mul_of_nonneg_right (bound order) (pow_nonneg radius.property _)
    _ = constant := by rw [mul_assoc, ← mul_pow, inv_mul_cancel₀ nonzero, one_pow, mul_one]

theorem canonical_expansion {function : E → F} {series : FormalMultilinearSeries ℝ E F}
    {center : E} {radius : ℝ≥0} (positive : 0 < radius)
    (expansion : HasFPowerSeriesOnBall function series center radius)
    (constant : ℝ)
    (bound : ∀ order, ‖coefficients function center order‖ ≤ constant * (radius : ℝ)⁻¹ ^ order) :
    HasFPowerSeriesOnBall function (coefficients function center) center radius := by
  refine ⟨radius_of_coefficient_bound _ radius positive constant bound,
    by exact_mod_cast positive, ?_⟩
  intro offset membership
  exact expansion.hasSum_iteratedFDeriv membership

theorem local_uniform {function : E → F} {center : E}
    (analytic : AnalyticAt ℝ function center) :
    ∃ radius : ℝ≥0, 0 < radius ∧ ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ point ∈ Metric.ball center (radius : ℝ),
        HasFPowerSeriesOnBall function (coefficients function point) point radius ∧
        ∀ order, ‖coefficients function point order‖ ≤ constant * (radius : ℝ)⁻¹ ^ order := by
  obtain ⟨series, expansionRadius, expansion⟩ := analytic
  obtain ⟨largeRadius, positiveLarge, lessLarge⟩ :=
    ENNReal.lt_iff_exists_nnreal_btwn.mp expansion.r_pos
  have largePositive : (0 : ℝ≥0) < largeRadius := by exact_mod_cast positiveLarge
  let radius : ℝ≥0 := largeRadius / 4
  have positive : 0 < radius := div_pos largePositive (by norm_num)
  have doubleLess : (radius : ENNReal) + (radius : ENNReal) < expansionRadius := by
    rw [← ENNReal.coe_add]
    apply lt_of_le_of_lt _ lessLarge
    exact_mod_cast (show radius + radius ≤ largeRadius from
      (le_of_eq (show radius + radius = largeRadius / 2 by dsimp [radius]; ring)).trans
        (div_le_self (show (0 : ℝ≥0) ≤ largeRadius from zero_le) (by norm_num)))
  have seriesBound : (radius : ENNReal) + (radius : ENNReal) < series.radius :=
    doubleLess.trans_le expansion.r_le
  let constant : ℝ := (∑' order,
    TernaryPeriodPolynomials.PlaneEisensteinContinuation.TranslatedSeries.originMajorant series radius radius order : ℝ≥0)
  have constantNonnegative : 0 ≤ constant := NNReal.coe_nonneg _
  refine ⟨radius, positive, constant, constantNonnegative, ?_⟩
  intro point membership
  let offset := point - center
  have offsetBound : ‖offset‖₊ ≤ radius := by
    exact_mod_cast (show ‖point - center‖ ≤ (radius : ℝ) from
      (show ‖point - center‖ < (radius : ℝ) by
        simpa only [Metric.mem_ball, dist_eq_norm] using membership).le)
  have offsetLess : (‖offset‖₊ : ENNReal) < expansionRadius :=
    (ENNReal.coe_le_coe.mpr offsetBound).trans_lt ((le_add_right le_rfl).trans_lt doubleLess)
  have remaining : (radius : ENNReal) ≤ expansionRadius - (‖offset‖₊ : ENNReal) := by
    apply ENNReal.le_sub_of_add_le_left ENNReal.coe_ne_top
    exact ((add_le_add (ENNReal.coe_le_coe.mpr offsetBound) le_rfl).trans_lt doubleLess).le
  have shifted : HasFPowerSeriesOnBall function (series.changeOrigin offset) point radius := by
    have expansionShift := (expansion.changeOrigin offsetLess).mono
      (by exact_mod_cast positive) remaining
    simpa only [offset, add_sub_cancel] using expansionShift
  have scaledBound (order : ℕ) :
      (radius : ℝ) ^ order * ‖series.changeOrigin offset order‖ ≤ constant := by
    have scaled := TernaryPeriodPolynomials.PlaneEisensteinContinuation.TranslatedSeries.changeOrigin_scaled_norm_bound
      series radius radius seriesBound offset offsetBound order
    have normEquality : ‖(radius : ℝ) ^ order • series.changeOrigin offset order‖ =
        (radius : ℝ) ^ order * ‖series.changeOrigin offset order‖ :=
      (norm_smul _ _).trans (congrArg (fun value : ℝ =>
        value * ‖series.changeOrigin offset order‖)
        (Real.norm_of_nonneg (pow_nonneg radius.property order)))
    apply (normEquality ▸ scaled).trans
    exact_mod_cast (TernaryPeriodPolynomials.PlaneEisensteinContinuation.TranslatedSeries.originMajorant_summable
      series radius radius seriesBound).le_tsum' order
  have coefficientBound (order : ℕ) :
      ‖coefficients function point order‖ ≤ constant * (radius : ℝ)⁻¹ ^ order := by
    have radiusPositive : (0 : ℝ) < radius := by exact_mod_cast positive
    have divided : ‖series.changeOrigin offset order‖ ≤ constant / (radius : ℝ) ^ order :=
      (le_div_iff₀ (pow_pos radiusPositive order)).mpr (by
      simpa only [mul_comm] using scaledBound order)
    exact (coefficients_norm_le shifted order).trans (by
      simpa only [div_eq_mul_inv, inv_pow] using divided)
  exact ⟨canonical_expansion positive shifted constant coefficientBound, coefficientBound⟩

theorem uniform_on_compact (function : E → F) (compact : Set E)
    (compactness : IsCompact compact) (analytic : ∀ point ∈ compact, AnalyticAt ℝ function point) :
    ∃ radius : ℝ≥0, 0 < radius ∧ ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ point ∈ compact,
        HasFPowerSeriesOnBall function (coefficients function point) point radius ∧
        ∀ order, ‖coefficients function point order‖ ≤ constant * (radius : ℝ)⁻¹ ^ order := by
  let property := fun set : Set E => ∃ radius : ℝ≥0, 0 < radius ∧ ∃ constant : ℝ,
    0 ≤ constant ∧ ∀ point ∈ set,
      HasFPowerSeriesOnBall function (coefficients function point) point radius ∧
      ∀ order, ‖coefficients function point order‖ ≤ constant * (radius : ℝ)⁻¹ ^ order
  change property compact
  apply compactness.induction_on (p := property)
  · exact ⟨1, zero_lt_one, 0, le_rfl, by simp⟩
  · intro small large inclusion larger
    obtain ⟨radius, positive, constant, nonnegative, bounded⟩ := larger
    exact ⟨radius, positive, constant, nonnegative, fun point member => bounded point (inclusion member)⟩
  · intro first second firstProperty secondProperty
    obtain ⟨firstRadius, firstPositive, firstConstant, firstNonnegative, firstBound⟩ := firstProperty
    obtain ⟨secondRadius, secondPositive, secondConstant, secondNonnegative, secondBound⟩ := secondProperty
    let radius := min firstRadius secondRadius
    let constant := max firstConstant secondConstant
    have positive : 0 < radius := lt_min firstPositive secondPositive
    have decrease (oldRadius : ℝ≥0) (oldPositive : 0 < oldRadius)
        (oldConstant : ℝ) (oldNonnegative : 0 ≤ oldConstant)
        (radiusLe : radius ≤ oldRadius) (constantLe : oldConstant ≤ constant)
        (point : E)
        (bounded : HasFPowerSeriesOnBall function (coefficients function point) point oldRadius ∧
          ∀ order, ‖coefficients function point order‖ ≤ oldConstant * (oldRadius : ℝ)⁻¹ ^ order) :
        HasFPowerSeriesOnBall function (coefficients function point) point radius ∧
          ∀ order, ‖coefficients function point order‖ ≤ constant * (radius : ℝ)⁻¹ ^ order := by
      refine ⟨bounded.1.mono (by exact_mod_cast positive) (by exact_mod_cast radiusLe), ?_⟩
      intro order
      apply (bounded.2 order).trans
      have inverseLe : (oldRadius : ℝ)⁻¹ ≤ (radius : ℝ)⁻¹ := by
        apply (inv_le_inv₀ (by exact_mod_cast oldPositive) (by exact_mod_cast positive)).mpr
        exact_mod_cast radiusLe
      exact mul_le_mul constantLe
        (pow_le_pow_left₀ (inv_nonneg.mpr oldRadius.property) inverseLe order)
        (pow_nonneg (inv_nonneg.mpr oldRadius.property) _) (oldNonnegative.trans constantLe)
    refine ⟨radius, positive, constant, firstNonnegative.trans (le_max_left _ _), ?_⟩
    intro point member
    rcases member with member | member
    · exact decrease firstRadius firstPositive firstConstant firstNonnegative
        (min_le_left _ _) (le_max_left _ _) point (firstBound point member)
    · exact decrease secondRadius secondPositive secondConstant secondNonnegative
        (min_le_right _ _) (le_max_right _ _) point (secondBound point member)
  · intro point member
    obtain ⟨radius, positive, constant, nonnegative, bounded⟩ := local_uniform (analytic point member)
    exact ⟨Metric.ball point radius, nhdsWithin_le_nhds (Metric.ball_mem_nhds point
      (by exact_mod_cast positive)), radius, positive, constant, nonnegative, bounded⟩

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.CompactTaylorBounds
