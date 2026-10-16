module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.BoundedFamilies

@[expose] public section


open scoped NNReal

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.PackedSeries

variable {Index Domain : Type} {Values : Index → Type}
variable [NormedAddCommGroup Domain] [NormedSpace ℝ Domain]
variable [∀ index, NormedAddCommGroup (Values index)] [∀ index, NormedSpace ℝ (Values index)]
variable [∀ index, CompleteSpace (Values index)]

open scoped Classical

def injection (order : ℕ) (index : Index)
    (coefficient : ContinuousMultilinearMap ℝ (fun _ : Fin order => Domain) (Values index)) :
    ContinuousMultilinearMap ℝ (fun _ : Fin order => Domain) (lp Values ⊤) :=
  (lp.singleContinuousLinearMap ℝ Values ⊤ index).compContinuousMultilinearMap coefficient

omit [∀ index, CompleteSpace (Values index)] in
theorem injection_norm_le (order : ℕ) (index : Index)
    (coefficient : ContinuousMultilinearMap ℝ (fun _ : Fin order => Domain) (Values index)) :
    ‖injection order index coefficient‖ ≤ ‖coefficient‖ := by
  apply ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg _)
  intro directions
  change ‖lp.single ⊤ index (coefficient directions)‖ ≤ _
  rw [lp.norm_single (by simp)]
  exact coefficient.le_opNorm directions

def pack (order : ℕ)
    (coefficients : ∀ index, ContinuousMultilinearMap ℝ (fun _ : Fin order => Domain) (Values index)) :
    ContinuousMultilinearMap ℝ (fun _ : Fin order => Domain) (lp Values ⊤) :=
  ∑' index, injection order index (coefficients index)

theorem injections_summable (order : ℕ)
    (coefficients : ∀ index, ContinuousMultilinearMap ℝ (fun _ : Fin order => Domain) (Values index))
    (summable : Summable (fun index => ‖coefficients index‖)) :
    Summable (fun index => injection order index (coefficients index)) :=
  summable.of_norm_bounded (fun index => injection_norm_le order index (coefficients index))

omit [∀ index, CompleteSpace (Values index)] in
theorem pack_norm_le (order : ℕ)
    (coefficients : ∀ index, ContinuousMultilinearMap ℝ (fun _ : Fin order => Domain) (Values index))
    (summable : Summable (fun index => ‖coefficients index‖)) :
    ‖pack order coefficients‖ ≤ ∑' index, ‖coefficients index‖ := by
  have normSummable := summable.of_nonneg_of_le (fun index => norm_nonneg (injection order index (coefficients index)))
    (fun index => injection_norm_le order index (coefficients index))
  exact (norm_tsum_le_tsum_norm normSummable).trans
    (Summable.tsum_le_tsum (fun index => injection_norm_le order index (coefficients index)) normSummable summable)

theorem pack_apply (order : ℕ)
    (coefficients : ∀ index, ContinuousMultilinearMap ℝ (fun _ : Fin order => Domain) (Values index))
    (summable : Summable (fun index => ‖coefficients index‖)) (directions : Fin order → Domain) (index : Index) :
    pack order coefficients directions index = coefficients index directions := by
  have summed := ContinuousMultilinearMap.hasSum_eval (injections_summable order coefficients summable).hasSum directions
  have mapped := (lp.evalCLM ℝ Values ⊤ index).hasSum summed
  have isolated := hasSum_single (f := fun other => (lp.single ⊤ other (coefficients other directions)) index) index
    (fun other inequality => lp.single_apply_ne ⊤ other (coefficients other directions) inequality.symm)
  have isolatedValue : HasSum (fun other => (lp.single ⊤ other (coefficients other directions)) index) (coefficients index directions) := by
    simpa only [lp.single_apply_self] using isolated
  exact mapped.unique isolatedValue

omit [∀ index, CompleteSpace (Values index)] in
theorem coefficient_summable (series : ∀ index, FormalMultilinearSeries ℝ Domain (Values index))
    (radius : ℝ≥0) (positive : 0 < radius) (majorant : Index → ℝ) (summable : Summable majorant)
    (bounded : ∀ index order, ‖series index order‖ * (radius : ℝ) ^ order ≤ majorant index) (order : ℕ) :
    Summable (fun index => ‖series index order‖) := by
  have radiusPositive : (0 : ℝ) < radius := by exact_mod_cast positive
  apply (summable.div_const ((radius : ℝ) ^ order)).of_nonneg_of_le (fun _ => norm_nonneg _)
  intro index
  exact (le_div_iff₀ (pow_pos radiusPositive order)).mpr (bounded index order)

def series (coordinates : ∀ index, FormalMultilinearSeries ℝ Domain (Values index)) :
    FormalMultilinearSeries ℝ Domain (lp Values ⊤) := fun order => pack order (fun index => coordinates index order)

omit [∀ index, CompleteSpace (Values index)] in
theorem radius_le (coordinates : ∀ index, FormalMultilinearSeries ℝ Domain (Values index))
    (radius : ℝ≥0) (positive : 0 < radius) (majorant : Index → ℝ) (summable : Summable majorant)
    (bounded : ∀ index order, ‖coordinates index order‖ * (radius : ℝ) ^ order ≤ majorant index) :
    (radius : ENNReal) ≤ (series coordinates).radius := by
  apply (series coordinates).le_radius_of_bound (∑' index, majorant index)
  intro order
  have summableCoefficient := coefficient_summable coordinates radius positive majorant summable bounded order
  calc
    _ ≤ (∑' index, ‖coordinates index order‖) * (radius : ℝ) ^ order :=
      mul_le_mul_of_nonneg_right (pack_norm_le order _ summableCoefficient) (pow_nonneg radius.property order)
    _ = ∑' index, ‖coordinates index order‖ * (radius : ℝ) ^ order := (tsum_mul_right).symm
    _ ≤ ∑' index, majorant index := Summable.tsum_le_tsum (fun index => bounded index order)
      (summableCoefficient.mul_right _) summable

theorem hasFPowerSeries (function : Domain → lp Values ⊤)
    (coordinates : ∀ index, FormalMultilinearSeries ℝ Domain (Values index))
    (radius : ℝ≥0) (positive : 0 < radius) (majorant : Index → ℝ) (summable : Summable majorant)
    (bounded : ∀ index order, ‖coordinates index order‖ * (radius : ℝ) ^ order ≤ majorant index)
    (expansions : ∀ index, HasFPowerSeriesOnBall (fun point => function point index) (coordinates index) 0 radius) :
    HasFPowerSeriesOnBall function (series coordinates) 0 radius := by
  have radiusBound := radius_le coordinates radius positive majorant summable bounded
  have radiusPositive : (0 : ENNReal) < radius := by exact_mod_cast positive
  refine ⟨radiusBound, radiusPositive, ?_⟩
  intro offset membership
  have summed := ((series coordinates).hasFPowerSeriesOnBall (radiusPositive.trans_le radiusBound)).hasSum
    (Metric.eball_subset_eball radiusBound membership)
  have equality : (series coordinates).sum (0 + offset) = function (0 + offset) := by
    apply Subtype.ext
    funext index
    have mapped := (lp.evalCLM ℝ Values ⊤ index).hasSum summed
    change HasSum (fun order => (series coordinates order (fun _ => offset)) index)
      (((series coordinates).sum (0 + offset)) index) at mapped
    have equalityTerms : (fun order => (series coordinates order (fun _ => offset)) index) =
        fun order => coordinates index order (fun _ => offset) := by
      funext order
      exact pack_apply order _ (coefficient_summable coordinates radius positive majorant summable bounded order) _ index
    rw [equalityTerms] at mapped
    exact mapped.unique ((expansions index).hasSum membership)
  exact equality ▸ summed

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.PackedSeries
