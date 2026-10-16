module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Analytic.Derivatives
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.BoundedFamilies
public import Mathlib.Analysis.Analytic.ChangeOrigin

@[expose] public section


open scoped NNReal

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.TranslatedSeries

abbrev OriginIndices (order : ℕ) :=
  (additional : ℕ) × {indices : Finset (Fin (order + additional)) // indices.card = additional}

noncomputable def originMajorant {Domain Target : Type}
    [NormedAddCommGroup Domain] [NormedSpace ℝ Domain]
    [NormedAddCommGroup Target] [NormedSpace ℝ Target]
    (series : FormalMultilinearSeries ℝ Domain Target) (shiftRadius coefficientRadius : ℝ≥0) (order : ℕ) : ℝ≥0 :=
  ∑' index : OriginIndices order,
    ‖series (order + index.1)‖₊ * shiftRadius ^ index.1 * coefficientRadius ^ order

theorem originMajorant_summable {Domain Target : Type}
    [NormedAddCommGroup Domain] [NormedSpace ℝ Domain]
    [NormedAddCommGroup Target] [NormedSpace ℝ Target]
    (series : FormalMultilinearSeries ℝ Domain Target) (shiftRadius coefficientRadius : ℝ≥0)
    (radiusBound : (shiftRadius : ENNReal) + (coefficientRadius : ENNReal) < series.radius) :
    Summable (originMajorant series shiftRadius coefficientRadius) := by
  have shiftBound : (shiftRadius : ENNReal) < series.radius :=
    (le_add_right le_rfl).trans_lt radiusBound
  have fiberSummable (order : ℕ) :
      Summable (fun index : OriginIndices order =>
        ‖series (order + index.1)‖₊ * shiftRadius ^ index.1 * coefficientRadius ^ order) :=
    (series.changeOriginSeries_summable_aux₂ shiftBound order).mul_right _
  exact (series.changeOriginSeries_summable_aux₁ radiusBound).sigma' fiberSummable

theorem changeOrigin_scaled_norm_bound {Domain Target : Type}
    [NormedAddCommGroup Domain] [NormedSpace ℝ Domain]
    [NormedAddCommGroup Target] [NormedSpace ℝ Target]
    (series : FormalMultilinearSeries ℝ Domain Target) (shiftRadius coefficientRadius : ℝ≥0)
    (radiusBound : (shiftRadius : ENNReal) + (coefficientRadius : ENNReal) < series.radius)
    (offset : Domain) (offsetBound : ‖offset‖₊ ≤ shiftRadius) (order : ℕ) :
    ‖(coefficientRadius : ℝ) ^ order • series.changeOrigin offset order‖ ≤
      (originMajorant series shiftRadius coefficientRadius order : ℝ) := by
  have shiftBound : (shiftRadius : ENNReal) < series.radius :=
    (le_add_right le_rfl).trans_lt radiusBound
  have offsetRadius : (‖offset‖₊ : ENNReal) < series.radius :=
    (ENNReal.coe_le_coe.mpr offsetBound).trans_lt shiftBound
  have bound := series.nnnorm_changeOrigin_le order offsetRadius
  have sumBound :
      (∑' index : OriginIndices order, ‖series (order + index.1)‖₊ * ‖offset‖₊ ^ index.1) ≤
      ∑' index : OriginIndices order, ‖series (order + index.1)‖₊ * shiftRadius ^ index.1 := by
    have lowerSummable : Summable (fun index : OriginIndices order =>
        ‖series (order + index.1)‖₊ * ‖offset‖₊ ^ index.1) :=
      series.changeOriginSeries_summable_aux₂ (r := ‖offset‖₊) offsetRadius order
    have upperSummable : Summable (fun index : OriginIndices order =>
        ‖series (order + index.1)‖₊ * shiftRadius ^ index.1) :=
      series.changeOriginSeries_summable_aux₂ (r := shiftRadius) shiftBound order
    have termBound (index : OriginIndices order) :
        ‖series (order + index.1)‖₊ * ‖offset‖₊ ^ index.1 ≤
        ‖series (order + index.1)‖₊ * shiftRadius ^ index.1 :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (show (0 : ℝ≥0) ≤ ‖offset‖₊ from zero_le) offsetBound index.1) (by positivity)
    exact Summable.tsum_le_tsum termBound lowerSummable upperSummable
  have scaledBound := mul_le_mul_of_nonneg_right (bound.trans sumBound)
    (show (0 : ℝ≥0) ≤ coefficientRadius ^ order from zero_le)
  have majorantEquality :
      (∑' index : OriginIndices order, ‖series (order + index.1)‖₊ * shiftRadius ^ index.1) * coefficientRadius ^ order =
      originMajorant series shiftRadius coefficientRadius order := by
    exact (NNReal.tsum_mul_right _ _).symm
  have realBound :
      ‖series.changeOrigin offset order‖ * (coefficientRadius : ℝ) ^ order ≤
      (originMajorant series shiftRadius coefficientRadius order : ℝ) := by
    exact_mod_cast (scaledBound.trans_eq majorantEquality)
  calc
    _ = ((coefficientRadius : ℝ) ^ order) * ‖series.changeOrigin offset order‖ :=
      (norm_smul _ _).trans (congrArg (fun value : ℝ => value * ‖series.changeOrigin offset order‖)
        (Real.norm_of_nonneg (pow_nonneg coefficientRadius.property order)))
    _ = ‖series.changeOrigin offset order‖ * (coefficientRadius : ℝ) ^ order := mul_comm _ _
    _ ≤ _ := realBound

noncomputable def translatedCoefficients {Domain Target : Type}
    [NormedAddCommGroup Domain] [NormedSpace ℝ Domain]
    [NormedAddCommGroup Target] [NormedSpace ℝ Target]
    (series : FormalMultilinearSeries ℝ Domain Target) (shiftRadius coefficientRadius : ℝ≥0)
    (radiusBound : (shiftRadius : ENNReal) + (coefficientRadius : ENNReal) < series.radius)
    (offset : {offset : Domain // ‖offset‖₊ ≤ shiftRadius}) :
    lp (fun order : ℕ => ContinuousMultilinearMap ℝ (fun _ : Fin order => Domain) Target) ⊤ :=
  ⟨fun order => (coefficientRadius : ℝ) ^ order • series.changeOrigin offset.val order,
    memℓp_infty (by
      refine ⟨(∑' order, originMajorant series shiftRadius coefficientRadius order : ℝ≥0), ?_⟩
      rintro value ⟨order, rfl⟩
      apply (changeOrigin_scaled_norm_bound series shiftRadius coefficientRadius radiusBound
        offset.val offset.property order).trans
      exact_mod_cast (originMajorant_summable series shiftRadius coefficientRadius radiusBound).le_tsum' order)⟩

theorem translatedCoefficients_apply {Domain Target : Type}
    [NormedAddCommGroup Domain] [NormedSpace ℝ Domain]
    [NormedAddCommGroup Target] [NormedSpace ℝ Target]
    (series : FormalMultilinearSeries ℝ Domain Target) (shiftRadius coefficientRadius : ℝ≥0)
    (radiusBound : (shiftRadius : ENNReal) + (coefficientRadius : ENNReal) < series.radius)
    (offset : {offset : Domain // ‖offset‖₊ ≤ shiftRadius}) (order : ℕ) :
    translatedCoefficients series shiftRadius coefficientRadius radiusBound offset order =
      (coefficientRadius : ℝ) ^ order • series.changeOrigin offset.val order := rfl

theorem translatedCoefficients_continuous {Domain Target : Type}
    [NormedAddCommGroup Domain] [NormedSpace ℝ Domain]
    [NormedAddCommGroup Target] [NormedSpace ℝ Target] [CompleteSpace Target]
    (series : FormalMultilinearSeries ℝ Domain Target) (shiftRadius coefficientRadius : ℝ≥0)
    (radiusBound : (shiftRadius : ENNReal) + (coefficientRadius : ENNReal) < series.radius) :
    Continuous (translatedCoefficients series shiftRadius coefficientRadius radiusBound) := by
  let _ : ∀ order : ℕ, CompleteSpace (ContinuousMultilinearMap ℝ (fun _ : Fin order => Domain) Target) :=
    fun _ => ContinuousMultilinearMap.instCompleteSpace
  have shiftBound : (shiftRadius : ENNReal) < series.radius :=
    (le_add_right le_rfl).trans_lt radiusBound
  have seriesPositive : 0 < series.radius := (zero_le : (0 : ENNReal) ≤ shiftRadius).trans_lt shiftBound
  apply continuousOn_univ.mp
  apply TernaryPeriodPolynomials.PlaneEisensteinContinuation.BoundedFamilies.continuousOn_of_summable_bound
    (translatedCoefficients series shiftRadius coefficientRadius radiusBound)
  · intro order
    have coefficientContinuous : Continuous (fun offset : {offset : Domain // ‖offset‖₊ ≤ shiftRadius} =>
        series.changeOrigin offset.val order) := by
      apply (series.hasFPowerSeriesOnBall_changeOrigin order seriesPositive).continuousOn.comp_continuous
        continuous_subtype_val
      intro offset
      simpa only [Metric.mem_eball, edist_nndist, nndist_zero_right] using
        (ENNReal.coe_le_coe.mpr offset.property).trans_lt shiftBound
    exact (coefficientContinuous.const_smul ((coefficientRadius : ℝ) ^ order)).continuousOn
  · exact NNReal.summable_coe.mpr (originMajorant_summable series shiftRadius coefficientRadius radiusBound)
  · intro offset _ order
    exact changeOrigin_scaled_norm_bound series shiftRadius coefficientRadius radiusBound offset.val offset.property order

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.TranslatedSeries
