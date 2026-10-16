module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Compact.AnalyticAverage
public import Mathlib.MeasureTheory.Constructions.UnitInterval
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section


open MeasureTheory Filter

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

noncomputable def segmentDerivativeAverage
    {D F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (function : D → F) (center displacement direction : D) : F :=
  ∫ time : unitInterval, fderiv ℝ function (center + (time : ℝ) • displacement) direction

theorem segmentDerivativeAverage_smul_direction
    {D F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (function : D → F) (center displacement direction : D) (scalar : ℝ) :
    segmentDerivativeAverage function center displacement (scalar • direction) =
      scalar • segmentDerivativeAverage function center displacement direction := by
  simp only [segmentDerivativeAverage, map_smul, integral_smul]

theorem segmentDerivativeAverage_comp_isometry
    {D F H : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    (isometry : F ≃ₗᵢ[ℝ] H) (function : D → F) (center displacement direction : D) :
    segmentDerivativeAverage (isometry ∘ function) center displacement direction =
      isometry (segmentDerivativeAverage function center displacement direction) := by
  unfold segmentDerivativeAverage
  simp only [isometry.comp_fderiv, ContinuousLinearMap.comp_apply]
  exact isometry.toLinearIsometry.integral_comp_comm _

theorem analyticAt_segmentDerivativeAverage
    {E D F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {function : E × D → F} {center : D}
    (analytic : AnalyticAt ℝ function (0, center)) :
    AnalyticAt ℝ (fun input : E × (D × D) =>
      segmentDerivativeAverage (fun point => function (input.1, point)) center input.2.1 input.2.2) 0 := by
  let derivative (input : E × (D × D)) : F :=
    fderiv ℝ (fun point => function (input.1, point)) (center + input.2.1) input.2.2
  have derivative_analytic : AnalyticAt ℝ derivative 0 := by
    have smooth : ContDiffAt ℝ ⊤
        (fun input : (E × (D × D)) × D => function (input.1.1, input.2)) (0, center + (0 : E × (D × D)).2.1) := by
      have original : ContDiffAt ℝ ⊤ function (0, center) := analytic.contDiffAt
      simpa [Function.comp_def] using
        original.comp ((0 : E × (D × D)), center) (contDiffAt_fst.fst.prodMk contDiffAt_snd)
    exact ((smooth.fderiv (contDiffAt_const.add contDiffAt_snd.fst) (show (⊤ : WithTop ℕ∞) + 1 ≤ ⊤ from le_top)).clm_apply
      contDiffAt_snd.snd).analyticAt
  let inner (time : unitInterval) : (E × (D × D)) →L[ℝ] (E × (D × D)) :=
    { toFun := fun input => (input.1, (time : ℝ) • input.2.1, input.2.2)
      map_add' := by intros; simp [smul_add]
      map_smul' := by intros; simp [smul_smul, mul_comm]
      cont := continuous_fst.prodMk ((continuous_const.smul continuous_snd.fst).prodMk continuous_snd.snd) }
  have inner_bound (time : unitInterval) : ‖inner time‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro input
    change ‖(input.1, (time : ℝ) • input.2.1, input.2.2)‖ ≤ 1 * ‖input‖
    rw [one_mul, Prod.norm_def, Prod.norm_def, Prod.norm_def, Prod.norm_def]
    gcongr
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg time.property.1]
    exact mul_le_of_le_one_left (norm_nonneg _) time.property.2
  have averaged := compact_transformed_analyticAt (volume : Measure unitInterval)
    derivative derivative_analytic inner (fun _ => ContinuousLinearMap.id ℝ F)
    (fun input => continuous_const.prodMk ((continuous_subtype_val.smul continuous_const).prodMk continuous_const))
    continuous_snd 1 inner_bound (fun _ => ContinuousLinearMap.norm_id_le)
  exact averaged

theorem segmentDerivativeAverage_eq_sub
    {D F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {function : D → F} {center displacement : D}
    (differentiable : ∀ time ∈ Set.Icc (0 : ℝ) 1, DifferentiableAt ℝ function (center + time • displacement))
    (continuous : ContinuousOn (fun time : ℝ => fderiv ℝ function (center + time • displacement)) (Set.Icc 0 1)) :
    segmentDerivativeAverage function center displacement displacement = function (center + displacement) - function center := by
  have derivative (time : ℝ) (member : time ∈ Set.uIcc (0 : ℝ) 1) :
      HasDerivAt (fun time : ℝ => function (center + time • displacement))
        (fderiv ℝ function (center + time • displacement) displacement) time := by
    have inside : time ∈ Set.Icc (0 : ℝ) 1 := by simpa only [Set.uIcc_of_le zero_le_one] using member
    convert (differentiable time inside).hasFDerivAt.comp_hasDerivAt time
      ((hasDerivAt_id time).smul_const displacement |>.const_add center) using 1 <;> simp [Function.comp_def]
  have continuous_evaluated : ContinuousOn (fun time : ℝ => fderiv ℝ function (center + time • displacement) displacement) (Set.uIcc 0 1) := by
    simpa only [Set.uIcc_of_le zero_le_one] using continuous.clm_apply continuousOn_const
  have integrable : IntervalIntegrable (fun time : ℝ => fderiv ℝ function (center + time • displacement) displacement) volume 0 1 :=
    continuous_evaluated.intervalIntegrable
  have equality := intervalIntegral.integral_eq_sub_of_hasDerivAt derivative integrable
  rw [segmentDerivativeAverage, unitInterval.measurePreserving_coe.integral_comp
    (MeasurableEmbedding.subtype_coe measurableSet_Icc)
    (fun time : ℝ => fderiv ℝ function (center + time • displacement) displacement),
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
  simpa only [one_smul, zero_smul, add_zero] using equality

theorem segmentDerivativeAverage_self_eventually
    {D F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {function : D → F} {center : D} (analytic : AnalyticAt ℝ function center) :
    ∀ᶠ displacement in nhds 0, segmentDerivativeAverage function center displacement displacement =
      function (center + displacement) - function center := by
  obtain ⟨radius, positive, analytic_on⟩ := analytic.exists_ball_analyticOnNhd
  filter_upwards [Metric.ball_mem_nhds (0 : D) positive] with displacement small
  have inside (time : ℝ) (member : time ∈ Set.Icc (0 : ℝ) 1) :
      center + time • displacement ∈ Metric.ball center radius := by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg member.1]
    exact (mul_le_of_le_one_left (norm_nonneg displacement) member.2).trans_lt (by simpa using small)
  apply segmentDerivativeAverage_eq_sub
  · intro time member
    exact (analytic_on _ (inside time member)).differentiableAt
  · intro time member
    have derivative_continuous := ((analytic_on _ (inside time member)).contDiffAt
      (n := 1)).continuousAt_fderiv (by norm_num)
    exact (derivative_continuous.comp (f := fun time : ℝ => center + time • displacement)
      (continuous_const.add (continuous_id.smul continuous_const)).continuousAt).continuousWithinAt

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
