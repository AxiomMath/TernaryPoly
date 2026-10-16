module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.TaylorIntegral
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.TranslatedSeries
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.BoundedFamilies

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open MeasureTheory
open scoped NNReal

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.TranslatedCoefficientAnalyticity


open TernaryPeriodPolynomials.PlaneEisensteinContinuation.TranslatedSeries

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

local instance {D G : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (order : ℕ) :
    NormedAddCommGroup (ContinuousMultilinearMap ℝ (fun _ : Fin order => D) G) :=
  ContinuousMultilinearMap.normedAddCommGroup'

local instance {D G : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (order : ℕ) :
    NormedSpace ℝ (ContinuousMultilinearMap ℝ (fun _ : Fin order => D) G) :=
  ContinuousMultilinearMap.normedSpace'

omit [CompleteSpace F] in
theorem scaled_changeOriginSeries_bound (series : FormalMultilinearSeries ℝ E F)
    (shiftRadius coefficientRadius : ℝ≥0) (positive : 0 < shiftRadius)
    (radiusBound : (shiftRadius : ENNReal) + (coefficientRadius : ENNReal) < series.radius)
    (order additional : ℕ) :
    ‖(coefficientRadius : ℝ) ^ order • series.changeOriginSeries order additional‖ ≤
      (originMajorant series shiftRadius coefficientRadius order : ℝ) *
        (shiftRadius : ℝ)⁻¹ ^ additional := by
  have shiftBound : (shiftRadius : ENNReal) < series.radius :=
    (le_add_right le_rfl).trans_lt radiusBound
  have summable := (series.changeOriginSeries_summable_aux₂ shiftBound order).mul_right
    (coefficientRadius ^ order)
  have fiberBound := NNReal.tsum_comp_le_tsum_of_inj summable
    (i := fun indices : {indices : Finset (Fin (order + additional)) // indices.card = additional} =>
      (⟨additional, indices⟩ : OriginIndices order)) (by intro first second equality; simpa using equality)
  have normBound := mul_le_mul_of_nonneg_right
    (series.nnnorm_changeOriginSeries_le_tsum order additional)
    (show 0 ≤ shiftRadius ^ additional * coefficientRadius ^ order from zero_le)
  have weighted : ‖series.changeOriginSeries order additional‖₊ *
      (shiftRadius ^ additional * coefficientRadius ^ order) ≤
        originMajorant series shiftRadius coefficientRadius order := by
    apply normBound.trans
    simpa only [originMajorant, ← NNReal.tsum_mul_right, mul_assoc] using fiberBound
  have weightedReal :
      ‖(coefficientRadius : ℝ) ^ order • series.changeOriginSeries order additional‖ *
        (shiftRadius : ℝ) ^ additional ≤ (originMajorant series shiftRadius coefficientRadius order : ℝ) := by
    have scalarNorm : ‖(coefficientRadius : ℝ) ^ order‖ = (coefficientRadius : ℝ) ^ order :=
      Real.norm_of_nonneg (pow_nonneg coefficientRadius.property order)
    rw [norm_smul, scalarNorm]
    have cast : ‖series.changeOriginSeries order additional‖ *
        ((shiftRadius : ℝ) ^ additional * (coefficientRadius : ℝ) ^ order) ≤
          (originMajorant series shiftRadius coefficientRadius order : ℝ) := by exact_mod_cast weighted
    convert cast using 1; ring
  have positiveReal : (0 : ℝ) < shiftRadius := by exact_mod_cast positive
  have cancel := mul_le_mul_of_nonneg_right weightedReal
    (show 0 ≤ (shiftRadius : ℝ)⁻¹ ^ additional from
      pow_nonneg (inv_nonneg.mpr shiftRadius.property) additional)
  have cancellation : (shiftRadius : ℝ) ^ additional * (shiftRadius : ℝ)⁻¹ ^ additional = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ positiveReal.ne', one_pow]
  rw [mul_assoc, cancellation, mul_one] at cancel
  exact cancel

abbrev Coefficients (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] :=
  lp (fun order : ℕ => ContinuousMultilinearMap ℝ (fun _ : Fin order => E) F) ⊤

def value (series : FormalMultilinearSeries ℝ E F) (coefficientRadius : ℝ≥0)
    (offset : E) : Coefficients E F :=
  ∫ order : ℕ, lp.single ⊤ order ((coefficientRadius : ℝ) ^ order • series.changeOrigin offset order)
    ∂Measure.count

def componentSeries (series : FormalMultilinearSeries ℝ E F) (coefficientRadius : ℝ≥0)
    (order : ℕ) : FormalMultilinearSeries ℝ E (Coefficients E F) :=
  (lp.singleContinuousLinearMap ℝ
    (fun order : ℕ => ContinuousMultilinearMap ℝ (fun _ : Fin order => E) F) ⊤ order).compFormalMultilinearSeries
      ((coefficientRadius : ℝ) ^ order • series.changeOriginSeries order)

omit [CompleteSpace F] in
theorem componentSeries_bound (series : FormalMultilinearSeries ℝ E F)
    (shiftRadius coefficientRadius : ℝ≥0) (positive : 0 < shiftRadius)
    (radiusBound : (shiftRadius : ENNReal) + (coefficientRadius : ENNReal) < series.radius)
    (order additional : ℕ) :
    ‖componentSeries series coefficientRadius order additional‖ ≤
      (originMajorant series shiftRadius coefficientRadius order : ℝ) * (shiftRadius : ℝ)⁻¹ ^ additional := by
  let inclusion := lp.singleContinuousLinearMap ℝ
    (fun order : ℕ => ContinuousMultilinearMap ℝ (fun _ : Fin order => E) F) ⊤ order
  have inclusionBound : ‖inclusion‖ ≤ 1 := by
    apply inclusion.opNorm_le_bound (by norm_num)
    intro coefficient
    change ‖lp.single (E := fun order : ℕ => ContinuousMultilinearMap ℝ (fun _ : Fin order => E) F)
      ⊤ order coefficient‖ ≤ 1 * ‖coefficient‖
    simpa only [one_mul] using (lp.norm_single (p := ⊤)
      (E := fun order : ℕ => ContinuousMultilinearMap ℝ (fun _ : Fin order => E) F)
      (by simp) order coefficient).le
  exact (inclusion.norm_compContinuousMultilinearMap_le _).trans
    ((mul_le_of_le_one_left (norm_nonneg _) inclusionBound).trans
      (scaled_changeOriginSeries_bound series shiftRadius coefficientRadius positive radiusBound order additional))

theorem value_analyticAt_zero (series : FormalMultilinearSeries ℝ E F)
    (shiftRadius coefficientRadius : ℝ≥0) (positive : 0 < shiftRadius)
    (radiusBound : (shiftRadius : ENNReal) + (coefficientRadius : ENNReal) < series.radius) :
    AnalyticAt ℝ (value series coefficientRadius) 0 := by
  have positiveENN : (0 : ENNReal) < shiftRadius := by exact_mod_cast positive
  have shiftBound : (shiftRadius : ENNReal) < series.radius :=
    (le_add_right le_rfl).trans_lt radiusBound
  have majorantSummable := NNReal.summable_coe.mpr
    (originMajorant_summable series shiftRadius coefficientRadius radiusBound)
  have integrable (additional : ℕ) :
      Integrable (fun order => componentSeries series coefficientRadius order additional) Measure.count := by
    apply integrable_count_iff.mpr
    exact (majorantSummable.mul_right _).of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun order => componentSeries_bound series shiftRadius coefficientRadius positive radiusBound order additional)
  apply (TaylorIntegral.hasFPowerSeriesOnBall Measure.count
    (fun order offset => lp.single ⊤ order
      ((coefficientRadius : ℝ) ^ order • series.changeOrigin offset order))
    (componentSeries series coefficientRadius) 0 shiftRadius positive
    (∑' order, (originMajorant series shiftRadius coefficientRadius order : ℝ))
    (fun order => ?_) integrable (fun additional => ?_)).analyticAt
  · exact (lp.singleContinuousLinearMap ℝ
      (fun order : ℕ => ContinuousMultilinearMap ℝ (fun _ : Fin order => E) F) ⊤ order).comp_hasFPowerSeriesOnBall
        (((series.hasFPowerSeriesOnBall_changeOrigin order (positiveENN.trans shiftBound)).mono
          positiveENN shiftBound.le).const_smul (c := (coefficientRadius : ℝ) ^ order))
  · calc
      _ ≤ ∫ order : ℕ, (originMajorant series shiftRadius coefficientRadius order : ℝ) *
          (shiftRadius : ℝ)⁻¹ ^ additional ∂Measure.count :=
        integral_mono (integrable additional).norm
          (integrable_count_iff.mpr (by
            simpa only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (NNReal.coe_nonneg _),
              abs_pow, abs_inv, abs_of_nonneg shiftRadius.property] using
                majorantSummable.mul_right ((shiftRadius : ℝ)⁻¹ ^ additional)))
          (fun order => componentSeries_bound series shiftRadius coefficientRadius positive radiusBound order additional)
      _ = _ := by
        rw [integral_mul_const, integral_countable (integrable_count_iff.mpr (by
          simpa only [Real.norm_eq_abs, abs_of_nonneg (NNReal.coe_nonneg _)] using majorantSummable))]
        simp [Measure.real]

theorem value_eq_translatedCoefficients (series : FormalMultilinearSeries ℝ E F)
    (shiftRadius coefficientRadius : ℝ≥0)
    (radiusBound : (shiftRadius : ENNReal) + (coefficientRadius : ENNReal) < series.radius)
    (offset : {offset : E // ‖offset‖₊ ≤ shiftRadius}) :
    value series coefficientRadius offset.val =
      translatedCoefficients series shiftRadius coefficientRadius radiusBound offset := by
  have summableNorm : Summable (fun order => ‖translatedCoefficients series shiftRadius
      coefficientRadius radiusBound offset order‖) :=
    (NNReal.summable_coe.mpr (originMajorant_summable series shiftRadius coefficientRadius radiusBound)).of_nonneg_of_le
      (fun _ => norm_nonneg _) (fun order =>
        changeOrigin_scaled_norm_bound series shiftRadius coefficientRadius radiusBound offset.val offset.property order)
  have sum := TernaryPeriodPolynomials.PlaneEisensteinContinuation.BoundedFamilies.hasSum_single_of_summable_norm
    (translatedCoefficients series shiftRadius coefficientRadius radiusBound offset) summableNorm
  have integrable : Integrable (fun order => lp.single ⊤ order
      (translatedCoefficients series shiftRadius coefficientRadius radiusBound offset order)) Measure.count := by
    apply integrable_count_iff.mpr
    simpa only [lp.norm_single (by simp : (0 : ENNReal) < ⊤)] using summableNorm
  change (∫ order : ℕ, lp.single ⊤ order
    (translatedCoefficients series shiftRadius coefficientRadius radiusBound offset order) ∂Measure.count) = _
  rw [integral_countable integrable]
  simpa only [Measure.real, Measure.count_singleton, ENNReal.toReal_one, one_smul] using sum.tsum_eq

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.TranslatedCoefficientAnalyticity
