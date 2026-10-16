module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Compact.PowerSeriesIntegral
public import Mathlib.Topology.ContinuousMap.Compact

@[expose] public section


namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

variable {X E F : Type*} [TopologicalSpace X] [CompactSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [CompactSpace X] [NormedSpace ℝ E] in
theorem continuousMap_update_evaluation {order : ℕ} [DecidableEq (Fin order)] (vectors : Fin order → C(X, E))
    (index : Fin order) (function : C(X, E)) (point : X) :
    (fun position => Function.update vectors index function position point) =
      Function.update (fun position => vectors position point) index (function point) := by
  funext position
  by_cases equal : position = index
  · subst position
    simp
  · simp [Function.update_of_ne equal]

noncomputable def continuousMapMultilinearMap {order : ℕ}
    (operator : ContinuousMultilinearMap ℝ (fun _ : Fin order => E) F) :
    MultilinearMap ℝ (fun _ : Fin order => C(X, E)) C(X, F) where
  toFun vectors := ⟨fun point => operator (fun index => vectors index point),
    operator.cont.comp (continuous_pi (fun index => (vectors index).continuous))⟩
  map_update_add' vectors index first second := by
    ext point
    change operator (fun position => Function.update vectors index (first + second) position point) =
      operator (fun position => Function.update vectors index first position point) +
        operator (fun position => Function.update vectors index second position point)
    simp only [continuousMap_update_evaluation, ContinuousMap.add_apply, operator.map_update_add]
  map_update_smul' vectors index scalar function := by
    ext point
    change operator (fun position => Function.update vectors index (scalar • function) position point) =
      scalar • operator (fun position => Function.update vectors index function position point)
    simp only [continuousMap_update_evaluation, ContinuousMap.smul_apply, operator.map_update_smul]

theorem continuousMapMultilinearMap_bound {order : ℕ}
    (operator : ContinuousMultilinearMap ℝ (fun _ : Fin order => E) F)
    (vectors : Fin order → C(X, E)) :
    ‖continuousMapMultilinearMap operator vectors‖ ≤ ‖operator‖ * ∏ index, ‖vectors index‖ := by
  apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg _) (Finset.prod_nonneg (fun _ _ => norm_nonneg _)))).mpr
  intro point
  exact (operator.le_opNorm (fun index => vectors index point)).trans
    (mul_le_mul_of_nonneg_left (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
      (fun index _ => (vectors index).norm_coe_le_norm point)) (norm_nonneg _))

noncomputable def continuousMapMultilinear {order : ℕ}
    (operator : ContinuousMultilinearMap ℝ (fun _ : Fin order => E) F) :
    ContinuousMultilinearMap ℝ (fun _ : Fin order => C(X, E)) C(X, F) :=
  (continuousMapMultilinearMap (X := X) operator).mkContinuous ‖operator‖
    (continuousMapMultilinearMap_bound operator)

theorem continuousMapMultilinear_apply {order : ℕ}
    (operator : ContinuousMultilinearMap ℝ (fun _ : Fin order => E) F)
    (vectors : Fin order → C(X, E)) (point : X) :
    continuousMapMultilinear operator vectors point = operator (fun index => vectors index point) := rfl

theorem continuousMapMultilinear_norm_le {order : ℕ}
    (operator : ContinuousMultilinearMap ℝ (fun _ : Fin order => E) F) :
    ‖continuousMapMultilinear (X := X) operator‖ ≤ ‖operator‖ :=
  MultilinearMap.mkContinuous_norm_le _ (norm_nonneg _) _

noncomputable def continuousMapPowerSeries (series : FormalMultilinearSeries ℝ E F) :
    FormalMultilinearSeries ℝ C(X, E) C(X, F) := fun order => continuousMapMultilinear (series order)

theorem continuousMapPowerSeries_radius_le (series : FormalMultilinearSeries ℝ E F) :
    series.radius ≤ (continuousMapPowerSeries (X := X) series).radius :=
  FormalMultilinearSeries.radius_le_of_le (fun order => continuousMapMultilinear_norm_le (series order))

theorem continuousMapPowerSeries_sum_apply [CompleteSpace F]
    (series : FormalMultilinearSeries ℝ E F) (function : C(X, E))
    (inside : function ∈ Metric.eball 0 (continuousMapPowerSeries (X := X) series).radius) (point : X) :
    (continuousMapPowerSeries series).sum function point = series.sum (function point) := by
  have equality := (ContinuousMap.evalCLM ℝ (M := F) point).map_tsum
    ((continuousMapPowerSeries (X := X) series).summable (x := function) inside)
  exact equality

omit [NormedSpace ℝ E] in
theorem continuousMap_evaluation_mem_eball (function : C(X, E)) (radius : ENNReal)
    (inside : function ∈ Metric.eball 0 radius) (point : X) :
    function point ∈ Metric.eball 0 radius := by
  rw [Metric.mem_eball, edist_zero_right] at inside ⊢
  apply lt_of_le_of_lt _ inside
  rw [ContinuousMap.enorm_eq_iSup_enorm]
  exact le_iSup (fun argument => ‖function argument‖ₑ) point

theorem continuousMapPowerSeries_sum_eq [CompleteSpace F]
    {function : E → F} {series : FormalMultilinearSeries ℝ E F} {center : E} {radius : ENNReal}
    (expansion : HasFPowerSeriesOnBall function series center radius)
    (input : C(X, E)) (inside : input ∈ Metric.eball 0 radius) (point : X) :
    (continuousMapPowerSeries series).sum input point = function (center + input point) := by
  have lifted_inside : input ∈ Metric.eball 0 (continuousMapPowerSeries (X := X) series).radius :=
    lt_of_lt_of_le inside (expansion.r_le.trans (continuousMapPowerSeries_radius_le series))
  rw [continuousMapPowerSeries_sum_apply series input lifted_inside]
  exact (expansion.sum (continuousMap_evaluation_mem_eball input radius inside point)).symm

theorem continuousMapPowerSeries_analyticAt_comp [CompleteSpace F]
    {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    {function : E → F} {series : FormalMultilinearSeries ℝ E F} {center : E} {radius : ENNReal}
    (expansion : HasFPowerSeriesOnBall function series center radius)
    (input : D → C(X, E)) (point : D) (analytic : AnalyticAt ℝ input point)
    (inside : input point ∈ Metric.eball 0 radius) :
    AnalyticAt ℝ (fun vector => (continuousMapPowerSeries series).sum (input vector)) point := by
  have outer := (continuousMapPowerSeries (X := X) series).analyticOnNhd _
    (lt_of_lt_of_le inside (expansion.r_le.trans (continuousMapPowerSeries_radius_le series)))
  exact outer.comp analytic

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
